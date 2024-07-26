/// Verification of WETH9

/*//////////////////////////////////////////////////////////////
                            METHODS
//////////////////////////////////////////////////////////////*/
methods {
    function totalSupply() external returns(uint256) envfree;
}

/*//////////////////////////////////////////////////////////////
                             GHOSTS
//////////////////////////////////////////////////////////////*/
ghost mathint g_depositSum {
    init_state axiom g_depositSum == to_mathint(nativeBalances[currentContract]);
}

ghost mathint g_withdrawSum {
    init_state axiom g_withdrawSum == 0;
}

ghost mathint g_sumOfBalances {
    init_state axiom g_sumOfBalances == to_mathint(nativeBalances[currentContract]);
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