predicate sortedDescending(a: array<int>)
  // To determine if an array is sorted descending: for all i < j, a[i] >= a[j]
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] >= a[j]
}


method BubbleSortDescending(a: array<int>)
  requires a.Length >= 0
  modifies a
  ensures sortedDescending(a)
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  // Step 1: Determine the array length
    var n := a.Length;


    // If the array is empty or has only one element, it is already sorted
    if n <= 1 {
        return;
    }


    // Step 2: Nested loops to select the maximum value
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      // The first i elements are in descending order relative to each other
      invariant forall k, l :: 0 <= k < l < i ==> a[k] >= a[l]
      invariant forall k, l :: 0 <= k < i && i <= l < n ==> a[k] >= a[l]
      // Preserve the multiset of elements
      invariant multiset(a[..]) == old(multiset(a[..]))
    {
        var m := i;
        var j := i + 1;
        while j < n
          invariant i+1 <= j <= n
          invariant i <= m < n
          // During inner loop, the largest element in the unsorted portion [0..n-i) is bubbled up
          invariant forall k :: i <= k < j ==> a[m] >= a[k]
          invariant multiset(a[..]) == old(multiset(a[..]))
        {
            // Step 3:Compare adjacent elements and swap if the left is smaller than the right
            if a[j] > a[m] { m := j; }
            j := j + 1;
        }
        if m != i {
             a[i], a[m] := a[m], a[i];
        }
        i := i + 1;

    }
}
