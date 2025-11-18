predicate sorted(a:array<int>)
//To determine if an array is sorted: for all i < j, a[i] <= a[j]
 reads a 
{
    forall i,j :: 0 <= i < j <a.Length ==> a[i]<= a[j] 
}
//SelectSort 
method SelectSort(a: array<int>)
 requires a.Length >= 0 //requires input array length >=0
 modifies a             //can only a modify  
 ensures sorted(a)      // The array is ultimately sorted in ascending order after algorithmus end.                 
 ensures multiset(a[..]) /*The elements of the sorted array are the same as the elements of */
 == old(multiset(a[..]))// the unsorted array (the elements are not changed).
                                                
{
    var n := a.Length;
    //i indicates the position where the correct minimum element should be placed, 
    //incrementing from 0 to n-1.
    var i:= 0;
    //Outer loop: In each round, swap the minimum value of the remaining part to a[i].
    while i < n 
      invariant 0 <= i <= n
      // The processed portion [0..i) must have already been sorted
      invariant forall k, l :: 0 <= k < l < i ==> a[k] <= a[l]
      // All elements in the processed interval ≤ All elements in the unprocessed interval
      invariant forall k, l :: 0 <= k < i && i <= l < n ==> a[k] <= a[l] 
      // Preserve the element unchanged (no elements are lost)
      invariant multiset(a[..]) == old(multiset(a[..]))
      modifies a
    {
        // minIndex: Records the position of the smallest element in the range i..n
        var minIndex := i;
        // j iterates through i+1..n to find the minimum value
        var j:= i+1;

        // Inner loop: Find the smallest element in a[i..n).
        while j < n
          invariant i < n
          invariant i <= minIndex < n
          invariant i+1 <= j <= n 
          // Maintenance: a[minIndex] is always the minimum value of the current interval i..j
          invariant forall k :: i <= k < j ==> a[minIndex] <=  a[k]
          modifies a
        {
            // If a smaller value is found, update minIndex.
            if a[j] < a[minIndex] {
                minIndex := j;
            }
            j:= j+1;
        }
        // After completing one round, swap the found minimum value to a[i].
        a[i],a[minIndex] := a[minIndex], a[i];
        // Next round of processing i+1
        i:= i+1;
    }
}

method PrintArr(a:array<int>)
   requires a.Length >= 0
{
    print "[";
    var i:= 0;
    while i < a.Length
     invariant 0 <= i <= a.Length
    {
        print a[i];
        if i < a.Length -1{
            print ", ";
        }
        i:=i+1;
    } 
    print "]\n";
}

method Main(){
    print "Hello world\n";
    var a:array<int>:= new int[][4,1,5,8,7,6,2];
    PrintArr(a);
    SelectSort(a);
    PrintArr(a);
}