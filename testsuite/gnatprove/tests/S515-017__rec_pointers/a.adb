procedure A with SPARK_Mode is
   type List;
   type List_Ptr is access List;
   type List is record
      Val  : Integer;
      Next : List_Ptr;
   end record;

   LNN : List_Ptr := new List'(Val => 3, Next => null);
   LN : List_Ptr := new List'(Val => 2, Next => LNN);
   L : List := (Val => 1, Next => LN);

begin
   declare
      N : access constant List := L.Next;
   begin
      declare
         M : access constant List := N.Next;
      begin
         pragma Assert (M.Val = 3);
         pragma Assert (N.Val = 2);
         pragma Assert (L.Val = 1);
      end;
   end;
end A; 
