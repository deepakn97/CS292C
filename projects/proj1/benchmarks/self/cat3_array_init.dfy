method Main() returns (dummy: int)
{
  var n: int;
  var target: int;
  var dp: array<int>;
  var i: int;
  var j: int;
  i := 0;
  n := *;
  target := *;
  dp := *;

  assume n > 0;
  while (i < n)
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k <= i ==> dp[k] == target
  {
    dp[i] := target;
    i := i + 1;
  }
  return 0;
}

