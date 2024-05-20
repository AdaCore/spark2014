with Ada.Unchecked_Deallocation;

procedure Safe_Pointers
    with SPARK_Mode
is
begin
    -- Basic manipulation of pointers

    declare
        type Ptr is access Integer;
        X : Ptr;
        Y : Ptr;

        procedure Free is new Ada.Unchecked_Deallocation (Integer, Ptr);

    begin
        X := new Integer'(42);
        -- Y := X;
        X.all := X.all + 1;
        -- Y.all := Y.all + 1;
        Free (X);
        -- Free (Y);
    end;

    -- Data structures with pointers

    declare
        type Node;
        type List is access Node;
        type Node is record
            Data : Integer;
            Next : List;
        end record;

        procedure Free is new Ada.Unchecked_Deallocation (Node, List);

        Head : List := new Node'(Data => 0,
                                 Next => new Node'(Data => 1,
                                                   Next => new Node'(Data => 2,
                                                                     Next => null)));
        Node1 : List := Head.Next;
        Node2 : List := Node1.Next;
    begin
        Head.Next := null;
        Node1.Next := Head;
        Node2.Next := Node1;
        Head := Node2;

        Free (Head.Next.Next);
        Free (Head.Next);
        Free (Head);
    end;
end Safe_Pointers;
