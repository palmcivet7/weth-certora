/// Verification of WETH9

/*//////////////////////////////////////////////////////////////
                            METHODS
//////////////////////////////////////////////////////////////*/
methods {
    function totalSupply() external returns(uint256) envfree;
    function balanceOf(address) external returns (uint256) envfree;
    function allowance(address, address) external returns (uint256) envfree;
}

/*//////////////////////////////////////////////////////////////
                          DEFINITIONS
//////////////////////////////////////////////////////////////*/
definition canIncreaseAllowance(method f) returns bool = 
	f.selector == sig:approve(address,uint256).selector;

definition cantDecreaseAllowance(method f) returns bool = 
	f.selector != sig:approve(address,uint256).selector || 
	f.selector != sig:transferFrom(address,address,uint256).selector;

definition canDecreaseBalance(method f) returns bool = 
	f.selector == sig:transfer(address,uint256).selector ||
	f.selector == sig:transferFrom(address,address,uint256).selector ||
    f.selector == sig:withdraw(uint256).selector;

definition cantDecreaseBalance(method f) returns bool = 
	f.selector != sig:transfer(address,uint256).selector ||
	f.selector != sig:transferFrom(address,address,uint256).selector ||
    f.selector != sig:withdraw(uint256).selector;

definition cantChangeBalance(method f) returns bool = 
	f.selector != sig:transfer(address,uint256).selector ||
	f.selector != sig:transferFrom(address,address,uint256).selector ||
    f.selector != sig:withdraw(uint256).selector ||
    f.selector != sig:deposit().selector;

definition canTransfer(method f) returns bool =
    f.selector == sig:transfer(address,uint256).selector ||
	f.selector == sig:transferFrom(address,address,uint256).selector;

definition depositOrWithdraw(method f) returns bool =
    f.selector == sig:withdraw(uint256).selector ||
    f.selector == sig:deposit().selector ||
    f.isFallback;

/*//////////////////////////////////////////////////////////////
                             GHOSTS
//////////////////////////////////////////////////////////////*/
ghost mathint g_sumOfBalances {
    init_state axiom g_sumOfBalances == to_mathint(nativeBalances[currentContract]);
}

ghost mathint g_depositSum {
    init_state axiom g_depositSum == to_mathint(nativeBalances[currentContract]);
}

ghost mathint g_withdrawSum {
    init_state axiom g_withdrawSum == 0;
}

ghost mathint g_balanceChanges {
    init_state axiom g_balanceChanges == 0;
}

/*//////////////////////////////////////////////////////////////
                             HOOKS
//////////////////////////////////////////////////////////////*/
hook Sload uint256 balance balanceOf[KEY address addr] {
    require g_sumOfBalances >= to_mathint(balance);
}

hook Sstore balanceOf[KEY address addr] uint256 newValue (uint256 oldValue) {
    g_sumOfBalances = g_sumOfBalances - to_mathint(oldValue) + to_mathint(newValue);
    if (newValue > oldValue) g_depositSum = g_depositSum + to_mathint(newValue - oldValue);
    else g_withdrawSum = g_withdrawSum + to_mathint(oldValue - newValue);

    g_balanceChanges = g_balanceChanges + 1;
}

/*//////////////////////////////////////////////////////////////
                           INVARIANTS
//////////////////////////////////////////////////////////////*/
invariant totalSupplyIsSumOfBalances()
    to_mathint(totalSupply()) == g_sumOfBalances
    {
        preserved with (env e) {
          require e.msg.sender != currentContract;
        }
    }

invariant solvencyDeposits()
    to_mathint(totalSupply()) == g_depositSum - g_withdrawSum
    {
        preserved with (env e) {
          require e.msg.sender != currentContract;
          requireInvariant totalSupplyIsSumOfBalances();
        }
    }

invariant depositorBalancesLteTotalSupply(address alice, address bob)
    balanceOf(alice) + balanceOf(bob) <= to_mathint(totalSupply())
    {
        preserved with (env e1) {
          require e1.msg.sender != currentContract;
          require alice != bob;
          requireInvariant solvencyDeposits();
        }
        preserved transfer(address to, uint256 amount) with (env e2) {
            require e2.msg.sender == alice || e2.msg.sender == bob;
            require to == alice || to == bob;
            require balanceOf(e2.msg.sender) >= amount;
        }
        preserved transferFrom(address from, address to, uint256 amount) with (env e3) {
            require from == alice || from == bob;
            require to == alice || to == bob;
            if (e3.msg.sender != from) require allowance(from, e3.msg.sender) >= amount;
            require balanceOf(from) >= amount;
        }
        preserved withdraw(uint256 amount) with (env e4) {
            require e4.msg.sender == alice || e4.msg.sender == bob;
            require balanceOf(e4.msg.sender) >= amount;
            require nativeBalances[currentContract] >= amount;
        }
    }

/*//////////////////////////////////////////////////////////////
                             RULES
//////////////////////////////////////////////////////////////*/
/// @notice transfer must move `amount` tokens from the sender's account to `recipient`
rule transferIntegrity(address recipient, uint amount) {
    requireInvariant totalSupplyIsSumOfBalances();
    
    env e;
    require e.msg.sender != currentContract;
    address sender = e.msg.sender;
    
    mathint balance_sender_before = balanceOf(sender);
    mathint balance_recip_before = balanceOf(recipient);

    transfer(e, recipient, amount);

    mathint balance_sender_after = balanceOf(sender);
    mathint balance_recip_after = balanceOf(recipient);

    assert recipient != sender => balance_sender_after == balance_sender_before - amount,
        "transfer must decrease sender's balance by amount";
    assert recipient != sender => balance_recip_after == balance_recip_before + amount,
        "transfer must increase recipient's balance by amount";
    assert recipient == sender => balance_sender_after == balance_sender_before,
        "transfer must not change sender's balancer when transferring to self";
}

/// @notice transfer reverts if sender's balance is too small
rule transferReverts(address recipient, uint amount) {
    requireInvariant totalSupplyIsSumOfBalances();

    env e;
    require e.msg.sender != currentContract;
    require balanceOf(e.msg.sender) < amount;

    transfer@withrevert(e, recipient, amount);
    assert lastReverted;
}

/// @notice transfer must not revert unless the sender doesn't have enough funds
rule transferDoesntRevert(address recipient, uint amount) {
    requireInvariant totalSupplyIsSumOfBalances();
    
    env e;
    require e.msg.sender != currentContract;
    require e.msg.sender != 0;
    require recipient != 0;
    require e.msg.value == 0;
    require balanceOf(e.msg.sender) >= amount;
    require balanceOf(recipient) + amount < max_uint;

    transfer@withrevert(e, recipient, amount);
    assert !lastReverted;
}

/// @notice transferFrom must move `amount` tokens from the sender's account to `recipient`
rule transferFromIntegrity(address owner, address recipient, uint amount) {
    requireInvariant totalSupplyIsSumOfBalances();

    env e;
    require e.msg.sender != currentContract;
    require balanceOf(owner) >= amount;
    if (e.msg.sender != owner) require allowance(owner, e.msg.sender) >= amount;
    
    mathint ownerStartingBalance = balanceOf(owner);
    mathint recipientStartingBalance = balanceOf(recipient);

    transferFrom(e, owner, recipient, amount);

    mathint ownerEndingBalance = balanceOf(owner);
    mathint recipientEndingBalance = balanceOf(recipient);

    assert recipient != owner => ownerEndingBalance == ownerStartingBalance - amount,
        "transfer must decrease owners's balance by amount";
    assert recipient != owner => recipientEndingBalance == recipientStartingBalance + amount,
        "transfer must increase recipient's balance by amount";
    assert recipient == owner => ownerEndingBalance == ownerStartingBalance,
        "transfer must not change owner's balancer when transferring to self";
}

/// @notice transferFrom reverts if owner's balance is too small
rule transferFromReverts(address owner, address recipient, uint amount) {
    requireInvariant totalSupplyIsSumOfBalances();

    env e;
    require e.msg.sender != currentContract;
    require balanceOf(owner) < amount;
    if (e.msg.sender != owner) require allowance(owner, e.msg.sender) >= amount;

    transferFrom@withrevert(e, owner, recipient, amount);
    assert lastReverted;
}

/// @notice transferfrom must not revert unless the owner doesn't have enough funds
rule transferFromDoesntRevert(address owner, address recipient, uint amount) {
    requireInvariant totalSupplyIsSumOfBalances();

    env e;
    require e.msg.sender != currentContract;
    require owner != 0;
    require recipient != 0;
    require e.msg.value == 0;
    require balanceOf(owner) >= amount;
    require balanceOf(recipient) + amount < max_uint;
    if (e.msg.sender != owner) require allowance(owner, e.msg.sender) >= amount;

    transferFrom@withrevert(e, owner, recipient, amount);
    assert !lastReverted;
}

/// @notice only the owner of the token can approve it for spending
rule allowanceIntegrity(address owner, address spender) {
    requireInvariant totalSupplyIsSumOfBalances();

    env e;
    method f;
    calldataarg args;
    require e.msg.sender != currentContract;

    mathint startingAllowance = allowance(owner, spender);
    f(e, args); // was: approve@withrevert(e, spender, amount);
    mathint endingAllowance = allowance(owner, spender);

    assert endingAllowance > startingAllowance => e.msg.sender == owner;
    assert endingAllowance > startingAllowance => canIncreaseAllowance(f);
    assert endingAllowance == startingAllowance => cantDecreaseAllowance(f);
}

/// @notice balance amounts should only decrease if transfers or withdraws happen
rule balanceOfIntegrity(address owner) {
    requireInvariant totalSupplyIsSumOfBalances();
    
    env e;
    method f;
    calldataarg args;
    require e.msg.sender != currentContract;

    mathint startingBalance = balanceOf(owner);
    f(e, args);
    mathint endingBalance = balanceOf(owner);

    assert endingBalance < startingBalance => canDecreaseBalance(f);
    assert endingBalance >= startingBalance => cantDecreaseBalance(f);
}

/// @notice ensure correct amount of balances are changed in any given transaction
rule balanceChangeIntegrity() {
    requireInvariant totalSupplyIsSumOfBalances();
    require g_balanceChanges == 0;
    
    env e;
    method f;
    calldataarg args;
    require e.msg.sender != currentContract;

    f(e, args);

    assert g_balanceChanges == 2 => canTransfer(f);
    assert g_balanceChanges == 1 => depositOrWithdraw(f);
    assert g_balanceChanges == 0 => cantChangeBalance(f);
}
