// def count(coins, n, target_sum):
//     # 2D dp array where n is the number of coin denominations and target_sum is the target sum
//     dp = [[0 for j in range(target_sum + 1)] for i in range(n + 1)]

//     # Represents the base case where the target sum is 0, and there is only one way to make change: by not selecting any coin
//     dp[0][0] = 1
//     for i in range(1, n + 1):
//         for j in range(target_sum + 1):
//             # Add the number of ways to make change without using the current coin
//             dp[i][j] += dp[i - 1][j]

//             if j - coins[i - 1] >= 0:
//                 # Add the number of ways to make change using the current coin
//                 dp[i][j] += dp[i][j - coins[i - 1]]

//     return dp[n][target_sum]
// Author: Deepak Nathani (dnathani@ucsb.edu)
// Category 3: Difny/\IMP programs with both arrays and loops
// array initialization to a target value

// not verified
// change loop invariant to 0 <= k < i ==> dp[k] == target
method arrayInit() returns (dummy: int)
{
  var n: int;
  var target: int;

  n := *;
  target := *;
  assume n > 0;

  var dp : array<int>;
  dp := *;
  assume dp != null;

  // set every element in the dp array to 0
  var i: int;
  var j: int;
  i := 0;

  while (i < n)
    decreases n - i
    invariant 0 <= i <= n
    invariant forall k: int:: 0 <= k <= i ==> dp[k] == target
  {
    dp[i] := target;
    i := i + 1;
  }
  return 0;
}

