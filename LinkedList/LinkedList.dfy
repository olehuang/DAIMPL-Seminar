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
        //insert Element in LinkedList in postion pos
        method InsertItem(v:int,pos:int)returns(value:int)
          requires 0 <= pos <= length
          modifies this
          ensures length == old(length) + 1
          ensures value == v
        {
            if pos == 0 {
             // Insert at head
             head := new Node(v, head);
            } else {
             // Traverse to node before pos
              var current := head;
             var i := 1;
             while i < pos
                 invariant 1 <= i <= pos
                 invariant current != null
             {
                 current := current.next;
                 i := i + 1;
             }

             // Insert new node
             var newNode := new Node(v, current.next);
             current.next := newNode;
            }
            length := length + 1;
            value := v;
        }
        //search Element in LinkedList
        method Find(pos:int) returns(value:int)
          requires 0 <= pos < length
          ensures true
        {
          var current := head;
          var i := 0;

          while i < pos 
            invariant 0 <= i <= pos
            invariant current!= null
          {
              current := current.next;
              i := i + 1;
           }

         value := current.value;
        }
        // delete Node 
        method Delete(pos:int) returns(value:int)
          requires 0 <= pos < length
          requires head!= null
          modifies this
          ensures length == old(length) - 1
        {
            if pos == 0 {
            // delete head
              value := head.value;
              head := head.next;
            }else {
            // find node before pos
              var current := head;
              var i := 1;

              while i < pos
                 invariant 1 <= i <= pos
                 invariant current != null
              {
                 current := current.next;
                 i := i + 1;
              }
             value := current.next.value;
             current.next := current.next.next;
            }
            length := length - 1;
        }

    }
}

