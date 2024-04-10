method max_arr(a: array<int>)  returns (r:int)
  // we assume this function can only be called with a is non-empty
  requires a.Length >= 1
  // r is no smaller than any element
  ensures forall i :: 0 <= i < a.Length ==> (r >= a[i])
  // r has to be one of the elements
  ensures exists i :: 0 <=i < a.Length && a[i] == r
{
  // current max
  var max := a[0];

  // an loop invariant is a logical formula that holds:
  // 1. before you enter the loop
  // 2. after every iteration of the loop
  for i := 1 to a.Length
    // this invariant is needed to prove the first "ensures"
    // intuitively, we say max is greater than or equal to all array elements up to i
    // which are the ones we have seen so far
    invariant forall j :: 0 <= j < i ==> (max >= a[j])
    // this invariant is needed to prove the second "ensures"
    // intuitively, we say max is one of the array elements up to i
    invariant exists i :: 0 <= i < a.Length && a[i] == max
  {
    if a[i] > max {
      max := a[i];
    }
  }

  // once the loop exits, we know that
  // the first invariant holds for i == a.Length, which means we know
  //   forall j :: 0 <= j < a.Length ==> (max >= a[j])
  // this proves the first "ensures"!
  // similarly, upon loop exit, the second loop invariant proves
  // the second "ensures"

  return max;
}