procedure Test_List with SPARK_Mode
is
   type List_Cell;
   type List is access List_Cell;
   type List_Cell is record
      Data : Integer;
      Next : List;
   end record;

  function Tail_2 (L : access List_Cell) return access List_Cell is
   (L.Next.Next)
     with Pre => L /= null and then L.Next /= null;

   X : List;
begin
   X := new List_Cell'(1, null);
   X.Next := new List_Cell'(2, null);
   X.Next.Next := new List_Cell'(3, null);
   X.Next.Next.Next := new List_Cell'(4, null);
   X.Next.Next.Next.Next := new List_Cell'(5, null);

   declare
      Y : access List_Cell := Tail_2 (X);
   begin
      Y.Data := 42;
   end;

   pragma Assert (X.Data = 1);
   pragma Assert (X.Next.Data = 2);
   pragma Assert (X.Next.Next.Data = 42);
   pragma Assert (X.Next.Next.Next.Data = 4);
end Test_List;
