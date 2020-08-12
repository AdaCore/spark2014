procedure Main with SPARK_Mode is
   X : Boolean;
   A : Boolean;

   Y1 : Positive :=
     (declare
        --  reads of uninitialized data by various declare items
        V : constant Boolean := X;
        Z : constant Boolean := not X;
        Foo : constant Integer := (if Z then 3 else 2);
        W : Boolean renames A;
      begin
        --  But don't use the data
        123);

   Y2 : Positive :=
     (declare
        Z : constant Boolean := X;
        W : Boolean renames Z;
      begin
      --  Actually use the contents of the declare item
        (if W then 123 else 321));
begin
   X := True;  --  dummy assignment, too late
end;
