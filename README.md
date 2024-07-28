# WETH Certora

This repo is to practice using Certora by verifying the WETH contract, and was inspired by [Horsefacts' weth invariant testing article/repo](https://github.com/horsefacts/weth-invariant-testing), and [Certora's Tutorials](https://docs.certora.com/en/latest/docs/user-guide/tutorials.html).

## Usage

Export your Certora Prover key as `CERTORAKEY` and then run:

```
certoraRun ./certora/conf/WETH9.conf`
```

## Notes

- `lastReverted` refers to last call made, so if we are making another call after the method we expected to revert, consider saving the `@withrevert` result in a boolean and checking it later

- `totalSupply()` can also be written as `nativeBalances[currentContract]` because the `WETH9.totalSupply()` returns `address(this).balance`. So this line:

```
to_mathint(totalSupply()) == g_depositSum - g_withdrawSum
```

can also be written as:

```
to_mathint(nativeBalances[currentContract]) == g_depositSum - g_withdrawSum
```
