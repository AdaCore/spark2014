procedure Local_Borrow_Array with SPARK_Mode is
   type Int_Acc is access Integer;
   type List;
   type List_Acc is access List;
   type List_Acc_Arr is array (Positive range <>) of List_Acc;
   type List_Acc_Arr_Acc is access List_Acc_Arr;
   type List is record
      V : Integer;
      N : List_Acc_Arr_Acc;
   end record;

   function Get_Nexts (X : access List) return access List_Acc_Arr with
     Pre => X /= null
   is
   begin
      return X.N;
   end Get_Nexts;

   X1 : constant List_Acc := new List'(V => 1, N => null);
   A1 : constant List_Acc_Arr_Acc := new List_Acc_Arr'(X1, null);
   X2 : constant List_Acc := new List'(V => 2, N => A1);
   A2 : constant List_Acc_Arr_Acc := new List_Acc_Arr'(X2, null);
   X3 : constant List_Acc := new List'(V => 3, N => A2);
   A3 : constant List_Acc_Arr_Acc := new List_Acc_Arr'(X3, null);
   X4 : constant List_Acc := new List'(V => 4, N => A3);
   X : List_Acc := X4;
begin
   declare
      Y : access List := Get_Nexts (Get_Nexts (Get_Nexts (X) (1)) (1)) (1);
   begin
      Y.V := 10;
   end;
end Local_Borrow_Array;
