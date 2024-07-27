/// Verification of WETH9

/*//////////////////////////////////////////////////////////////
                            METHODS
//////////////////////////////////////////////////////////////*/
methods {
    function totalSupply() external returns(uint256) envfree;
    function balanceOf(address) external returns (uint256) envfree;
    function transfer(address, uint256) external returns (bool);
    function allowance(address, address) external returns (uint256) envfree;
    function approve(address, uint256) external returns (bool);
}

/*//////////////////////////////////////////////////////////////
                          DEFINITIONS
//////////////////////////////////////////////////////////////*/
definition ZERO_ADDRESS() returns address = 0x0000000000000000000000000000000000000000;

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

invariant totalSupplyIsDepositMinusWithdraw()
    to_mathint(totalSupply()) == g_depositSum - g_withdrawSum
    {
        preserved with (env e) {
          require e.msg.sender != currentContract;
        }
    }

/*//////////////////////////////////////////////////////////////
                             RULES
//////////////////////////////////////////////////////////////*/
/// @notice transfer must move `amount` tokens from the sender's account to `recipient`
rule transferIntegrity(address recipient, uint amount) {
    env e;
    require e.msg.sender != currentContract;
    
    mathint balance_sender_before = balanceOf(e.msg.sender);
    mathint balance_recip_before = balanceOf(recipient);

    transfer(e, recipient, amount);

    mathint balance_sender_after = balanceOf(e.msg.sender);
    mathint balance_recip_after = balanceOf(recipient);

    address sender = e.msg.sender;

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
    // `lastReverted` refers to last call made, so if we are making another call after the method we expected to revert,
    // consider saving the @withrevert result in a boolean and checking it later
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

/// @notice only the holder/owner of the token can approve it for spending
rule allowanceIntegrity(address holder, address spender) {
    env e;
    method f;
    calldataarg args;
    require e.msg.sender != currentContract;

    mathint startingAllowance = allowance(holder, spender);

    f(e, args); // was: approve@withrevert(e, spender, amount);

    mathint endingAllowance = allowance(holder, spender);

    assert endingAllowance > startingAllowance => e.msg.sender == holder;
    assert endingAllowance > startingAllowance => f.selector == sig:approve(address,uint).selector;
    assert endingAllowance == startingAllowance => (
        f.selector != sig:approve(address,uint).selector ||
        f.selector != sig:transferFrom(address,address,uint).selector
    );
}