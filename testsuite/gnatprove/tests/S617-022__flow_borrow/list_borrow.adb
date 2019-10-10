procedure List_Borrow with SPARK_Mode is
   type List_Cell;
   type List is access List_Cell;
   type List_Cell is record
      Value : Integer;
      Next  : List;
   end record;

   X1 : List := new List_Cell'(Value => 1, Next => null);
   X2 : List := new List_Cell'(Value => 2, Next => X1);
   X  : List := new List_Cell'(Value => 3, Next => X2);
begin
   declare
      Y : access List_Cell := X;
   begin
      Y := Y.Next;
      Y.Value := 1;
   end;
   pragma Assert (X.Value = 3);
   pragma Assert (X.Next.Next.Value = 1);
   pragma Assert (X.Next.Value = 1);
end List_Borrow;
