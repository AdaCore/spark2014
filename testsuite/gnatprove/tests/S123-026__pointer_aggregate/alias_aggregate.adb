procedure Alias_Aggregate with SPARK_Mode is
    type List_Cell;
    type List is access List_Cell;
    type List_Cell is record
       Value : Integer;
       Next1 : List;
       Next2 : List;
    end record;

    type Array_Cell is array (1 .. 5) of List;

    procedure Local (Y : List) with Pre => True is
       X : constant List_Cell := (Value => 1, others => Y);
    begin
       pragma Assert (X.Value = 2);
    end Local;

    procedure Local2 (Y : List) with Pre => True is
       Z : constant Array_Cell := (others => Y);
    begin
       null;
    end Local2;
begin
   null;
end Alias_Aggregate;
