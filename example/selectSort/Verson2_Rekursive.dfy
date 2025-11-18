predicate sorted(a:array<int>)
//To determine if an array is sorted: for all i < j, a[i] <= a[j]
 reads a 
{
    forall i,j :: 0 <= i < j <a.Length ==> a[i]<= a[j] 
}

function findMin(a: array<int>,start:int):int
    requires 0 <= start < a.Length
    reads a
    ensures start <= findMin(a,start) < a.Length
    ensures forall k :: start <= k < a.Length ==> a[findMin(a, start)] <= a[k]
    decreases a.Length - start
{
    if start == a.Length - 1 then start
    else
        var rest := findMin(a, start + 1);
        if a[start] <= a[rest] then start else rest
}

method SelectSort(a: array<int>)
 requires a.Length >= 0
 modifies a 
 ensures sorted(a)
{
    var n := a.Length;

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
        var minIndex := findMin(a, i);
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