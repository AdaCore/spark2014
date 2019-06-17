procedure List_Borrow with SPARK_Mode is
   type List_Cell;
   type List is access List_Cell;
   type List_Cell is record
      Value : Integer;
      Next  : List;
   end record;
   function All_Pos (X : List) return Boolean is
     (if X /= null then X.Value > 0
      and then All_Pos (X.Next));
   pragma Annotate (GNATprove, Terminating, All_Pos);

   subtype List_Pos is List with
     Predicate => All_Pos (List (List_Pos));

   X1 : List_Pos := new List_Cell'(Value => 1, Next => null);
   X2 : List_Pos := new List_Cell'(Value => 2, Next => X1);
   X  : List_Pos := new List_Cell'(Value => 3, Next => X2);

   Z1 : List_Pos := new List_Cell'(Value => 1, Next => null);
   Z2 : List_Pos := new List_Cell'(Value => 2, Next => Z1);
   Z  : List_Pos := new List_Cell'(Value => 3, Next => Z2);
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

   declare
      Y : access List_Cell := Z; --@PREDICATE_CHECK:FAIL
   begin
      Y := Y.Next;
      Y.Value := -1;
   end;
end List_Borrow;
