// Check if array a[start:end] is ordered. Here end is inclusive.
ghost predicate Ordered(a: array<int>, start: int, end: int)
  reads a
  requires a.Length >= 1
{
  forall i: int, j: int :: 0 <= start <= i <= j <= end < a.Length ==> a[i] <= a[j]
}

// If the array is partitioned at i, check that all the elements in right side partition are bigger than elements in left side partition. Bubbling the larger elements towards the end of array is a bubble sort property.
ghost predicate bubble(a: array<int>, i: int)
  reads a
  requires a.Length >= 1
{
  forall j, k: int :: 0 <= j <= i < k < a.Length ==> a[j] <= a[k]
}

// To check if the elements and their counts in the array are preserved.
twostate predicate Preserved(a: array<int>)
  reads a
{
  multiset(a[..]) == multiset(old(a[..]))
}

method bubble_sort(a: array<int>)
  modifies a
  requires a.Length >= 1
  ensures Ordered(a, 0, a.Length-1)
  ensures Preserved(a)
{
  var i : int := a.Length - 1;
  while i > 0
    // write invariants here
    // 1. invariant that i is increasing to prove termination
    invariant 0 <= i < a.Length
    // 2. invariant to prove that the subarray a[i:a.Length-1] is ordered
    invariant Ordered(a, i, a.Length-1)
    // 3. invariant to prove the all numbers in right side partition are bigger than numbers in left side
    invariant bubble(a, i)

    // add invariant that the array is always preserved
    invariant Preserved(a)

  {

    var j : int := 0;
    while j < i
      // write invariants here
      // 1. invariant that j to prove termination
      invariant 0 < i < a.Length && 0 <= j <= i

      // check that the element at current index j is larger than all the elements to it's left. This tells us that the algorithm is correctly bubbling up the largest number in this iteration.
      invariant forall k :: 0 <= k <= j ==> a[k] <= a[j]
      invariant bubble(a, i)
      invariant Ordered(a, i, a.Length-1)
      invariant Preserved(a)
    {
      if a[j] > a[j+1] {
        // swap the two numbers
        var temp : int := a[j];
        a[j] := a[j+1];
        a[j+1] := temp;
      }
      j := j + 1;
    }
    i := i - 1;
  }
}

method Main()
{
  var a: array<int> := new int[4];
  a[0] := 6; a[1] := 5; a[2] := 3; a[3] := 0;
  bubble_sort(a);
  print a[..];
}