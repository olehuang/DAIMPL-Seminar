module LinkedList{
    class Node{
        var value : int
        var next : Node?
        constructor(v:int,n:Node?)
           ensures value == v && next == n
        {
            value := v;
            next := n;
        }
    }
    class LinkedList{
        var head : Node?
        var length : nat 
        constructor()
           ensures head == null
           ensures length == 0
        {
            head := null;
            length := 0;
        }

        method Insert(v:int)
           modifies this
           ensures length == old(length) + 1
           ensures head != null && head.value == v
        {
            head := new Node(v,head);
            length := length + 1;
        }

    }
}

