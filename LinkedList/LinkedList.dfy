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

        method Insert(pos: nat, value:int)
           modifies this
           requires pos <= length
           ensures length == old(length) + 1
        {
            if pos == 0{
                var n := new Node(value,head);
                head := n;
                length := length +1;
                return;
            }

            var curr := head;
            var i := 0;
            while i < pos -1
              invariant 0 <= i <= pos - 1
              invariant curr != null 
            {
                curr := curr.next;
                i := i+1;
            }
            var newNode := new Node(value,curr.next);
            curr.next := newNode;
            length := length + 1;
        }

    }
}

