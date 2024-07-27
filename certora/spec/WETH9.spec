/// Verification of WETH9

/*//////////////////////////////////////////////////////////////
                            METHODS
//////////////////////////////////////////////////////////////*/
methods {
    function totalSupply() external returns(uint256) envfree;
    function balanceOf(address) external returns (uint256) envfree;
    function transfer(address, uint256) external returns (bool);
}

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
/// @title Transfer must move `amount` tokens from the caller's account to `recipient`
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