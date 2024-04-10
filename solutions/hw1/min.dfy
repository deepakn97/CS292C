method min2D(a: array<array<int>>)
  returns (r: int)
  // assume this function can only be called with a non-empty array
  requires a.Length >= 1 && forall i :: 0 <= i < a.Length ==> a[i].Length >= 1

  // ensure r is no larger than any element in the array
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a[i].Length ==> (r <= a[i][j])

  // ensure r exists in the array
  ensures exists i, j :: (0 <= i < a.Length && 0 <= j < a[i].Length) && (a[i][j] == r)
{
  var min := a[0][0];
  for i := 0 to a.Length
    // this invariant is for proving the first ensure statement
    invariant forall k, l :: (0 <= k < i && 0 <= l < a[k].Length) ==> min <= a[k][l]

    // this invariant is for proving the second ensure statement
    invariant exists k, l :: (0 <= k < a.Length && 0 <= l < a[k].Length) && (a[k][l] == min)
  {
    for j := 0 to a[i].Length

      // first write an invariants for the subarrays a[0] to a[i-1] inclusive
      invariant forall k, l :: (0 <= k < i && 0 <= l < a[k].Length) ==> (a[k][l] >= min)

      // then write an invariant specifically checking for the subarray a[i] upto j-1 index
      invariant forall l :: (0 <= l < j) ==> (a[i][l] >= min)

      // invariant to prove the second ensure statement
      invariant exists k, l :: (0 <= k < a.Length && 0 <= l < a[k].Length) && (a[k][l] == min)
    {
      if a[i][j] < min {
        min := a[i][j];
      }
    }
  }
  return min;
}