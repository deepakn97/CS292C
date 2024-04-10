predicate Ordered(a: array<int>)
  reads a
{
  forall i: int, j:int ::
    0 <= i <= j < a.Length ==>
      a[i] <= a[j]
}

method bubble_sort(a: array<int>)
  modifies a
  ensures Ordered(a)
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var i : int := 0;
  while i < a.Length
    // write invariants here
    // 1. invariant that i is increasing to prove termination
    decreases a.Length - i
    invariant 0 <= i <= a.Length
    // 2. invariant to prove that the subarray a[a.Length - i - 1:a.Length] is ordered
    // how to use ordered predicate here? Slicing the array return a seq<int> and I can't seem to typecast it back to array<int>.
    invariant forall j: int, k: int :: (a.Length-i-1 <= j <= k < a.Length) && (0 <= j <= k < a.Length) ==> a[j] <= a[k]

  {
    var j : int := 0;
    while j < a.Length - i - 1
      // write invariants here
      // 1. invariant that j to prove termination
      decreases a.Length - i - 1 - j
      invariant 0 <= j <= a.Length - i - 1

      // invariant to prove
    {
      if a[j] > a[j+1] {
        // swap the two numbers
        var temp : int := a[j];
        a[j] := a[j+1];
        a[j+1] := temp;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}

method Main()
{
  var a: array<int> := new int[4];
  a[0] := 6; a[1] := 5; a[2] := 3; a[3] := 0;
  bubble_sort(a);
  print a[..];
}