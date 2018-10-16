package body Pointers with SPARK_Mode is

   procedure Swap (X, Y : T_Ptr) is
      Tmp : T := X.all;
   begin
      X.all := Y.all;
      Y.all := Tmp;
   end Swap;

   procedure Swap (A : in out T_Arr; I, J : Index) is
      Tmp : T_Ptr := new T'(0);
   begin
      Swap (A(I), Tmp);
      Swap (A(J), Tmp);
      Swap (A(I), Tmp);
   end Swap;

end Pointers;
