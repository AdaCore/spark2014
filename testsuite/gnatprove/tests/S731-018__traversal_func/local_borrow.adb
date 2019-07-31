procedure Local_Borrow with SPARK_Mode is
   type Int_Acc is access Integer;
   type List;
   type List_Acc is access List;
   type List is record
      V : Integer;
      N : List_Acc;
   end record;

   function Get_Next (X : access List) return access List with
     Pre => X /= null
   is
   begin
      return X.N;
   end Get_Next;

   X1 : constant List_Acc := new List'(V => 1, N => null);
   X2 : constant List_Acc := new List'(V => 2, N => X1);
   X3 : constant List_Acc := new List'(V => 3, N => X2);
   X4 : constant List_Acc := new List'(V => 4, N => X3);
   X : List_Acc := X4;
begin
   declare
      Y : access List := Get_Next (Get_Next (Get_Next (X)));
   begin
      Y.V := 10;
   end;
end Local_Borrow;
