package Incomplete_Types with SPARK_Mode is
    type List_Cell;
    type List is access List_Cell;
    type List_Cell is record
       Value : Integer;
       Next  : List;
    end record;

    X : constant List_Cell := (Value => 1, Next => null);
    pragma Assert (X.Value = 2);
end Incomplete_Types;
