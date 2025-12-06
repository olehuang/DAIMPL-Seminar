method SelectSort(a: array<int>)
 modifies a             
{
    var n := a.Length;
    var i:= 0;
    while i < n
    {
        var minIndex := i;
        var j:= i+1;
        while j < n
         invariant i <= minIndex < n
         invariant i+1 <= j <= n
        {
            
            if a[j] < a[minIndex] {
                minIndex := j;
            }
            j:= j+1;
        }
        a[i],a[minIndex] := a[minIndex], a[i];
        i:= i+1;
    }
}
//Print the elements of the array
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
    var a:array<int>:= new int[][4,1,5,8,7,3,6,2];
    PrintArr(a);//unsorted Array
    SelectSort(a); // selectSort reference
    PrintArr(a); // sorted Array
}