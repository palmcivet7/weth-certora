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
definition ZERO_ADDRESS() returns address = 0x0000000000000000000000000000000000000000;

definition canIncreaseAllowance(method f) returns bool = 
	f.selector == sig:approve(address,uint256).selector;

definition cantDecreaseAllowance(method f) returns bool = 
	f.selector != sig:approve(address,uint256).selector || 
	f.selector != sig:transferFrom(address,address,uint256).selector;

definition canDecreaseBalance(method f) returns bool = 
	f.selector == sig:transfer(address,uint256).selector ||
	f.selector == sig:transferFrom(address,address,uint256).selector ||
    f.selector == sig:withdraw(uint).selector;

definition cantDecreaseBalance(method f) returns bool = 
	f.selector != sig:transfer(address,uint256).selector ||
	f.selector != sig:transferFrom(address,address,uint256).selector ||
    f.selector != sig:withdraw(uint).selector;


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
        }
    }

invariant singleDepositorBalanceLteTotalSupply(address account)
    balanceOf(account) <= totalSupply()
    {
        preserved with (env e1) {
          require e1.msg.sender != currentContract;
        }
        preserved transfer(address to, uint256 amount) with (env e2) {
            require e2.msg.sender == account;
            require balanceOf(e2.msg.sender) >= amount;
        }
        preserved transferFrom(address from, address to, uint256 amount) with (env e3) {
            require from == account;
            require balanceOf(from) >= amount;
            if (e3.msg.sender != from) require allowance(from, e3.msg.sender) >= amount;
        }
        preserved withdraw(uint256 amount) with (env e4) {
            require e4.msg.sender == account;
            require balanceOf(e4.msg.sender) >= amount;
            require nativeBalances[currentContract] >= amount;
        }
    }

invariant depositorBalancesLteTotalSupply(address alice, address bob)
    balanceOf(alice) + balanceOf(bob) <= to_mathint(totalSupply())
    {
        preserved with (env e1) {
          require e1.msg.sender != currentContract;
          require alice != bob;
        }
        preserved transfer(address to, uint256 amount) with (env e2) {
            require (e2.msg.sender == alice && to == bob) || (
                e2.msg.sender == bob && to == alice
            );
            require balanceOf(e2.msg.sender) >= amount;
        }
        preserved transferFrom(address from, address to, uint256 amount) with (env e3) {
            require (from == alice && to == bob) || (from == bob && to == alice);
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
    env e;
    require e.msg.sender != currentContract;
    require balanceOf(e.msg.sender) < amount;

    transfer@withrevert(e, recipient, amount);
    assert lastReverted;
}

/// @notice transfer must not revert unless the sender doesn't have enough funds
rule transferDoesntRevert(address recipient, uint amount) {
    env e;
    require e.msg.sender != currentContract;
    require e.msg.sender != ZERO_ADDRESS();
    require recipient != ZERO_ADDRESS();
    require e.msg.value == 0;
    require balanceOf(e.msg.sender) >= amount;
    require balanceOf(recipient) + amount < max_uint;

    transfer@withrevert(e, recipient, amount);
    assert !lastReverted;
}

/// @notice transferFrom must move `amount` tokens from the sender's account to `recipient`
rule transferFromIntegrity(address owner, address recipient, uint amount) {
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
    env e;
    require e.msg.sender != currentContract;
    require balanceOf(owner) < amount;
    if (e.msg.sender != owner) require allowance(owner, e.msg.sender) >= amount;

    transferFrom@withrevert(e, owner, recipient, amount);
    assert lastReverted;
}

/// @notice transferfrom must not revert unless the owner doesn't have enough funds
rule transferFromDoesntRevert(address owner, address recipient, uint amount) {
    env e;
    require e.msg.sender != currentContract;
    require owner != ZERO_ADDRESS();
    require recipient != ZERO_ADDRESS();
    require e.msg.value == 0;
    require balanceOf(owner) >= amount;
    require balanceOf(recipient) + amount < max_uint;
    if (e.msg.sender != owner) require allowance(owner, e.msg.sender) >= amount;

    transferFrom@withrevert(e, owner, recipient, amount);
    assert !lastReverted;
}

/// @notice only the owner of the token can approve it for spending
rule allowanceIntegrity(address owner, address spender) {
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