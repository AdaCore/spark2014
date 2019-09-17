procedure Borrow_With_Variables with SPARK_Mode is
    type Tree;
    type Tree_Access is access Tree;
    type Tree_Access_Array is array (Positive range 1 .. 3) of Tree_Access;
    type Tree is record
       Value : Integer;
       Nexts : Tree_Access_Array;
    end record;

    X1 : Tree_Access := new Tree'(Value => 1, Nexts => <>);
    X2 : Tree_Access := new Tree'(Value => 1, Nexts => <>);
    X3 : Tree_Access := new Tree'(Value => 1, Nexts => <>);
    X  : Tree_Access := new Tree'(Value => 1, Nexts => (X1, X2, X3));
begin
    declare
       I : Integer := 1;
       Y : access Tree := X.Nexts (I);
       Z : access Tree := X.Nexts (X.Value);
    begin
       Y.Value := 2;
       I := 2;
    end;
    pragma Assert (X.Nexts (1).Value = 2);
    pragma Assert (X.Nexts (2).Value = 2);
end Borrow_With_Variables;
