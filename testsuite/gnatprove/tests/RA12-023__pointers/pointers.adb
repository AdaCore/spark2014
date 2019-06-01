package body Pointers with SPARK_Mode is

   procedure Swap (X, Y : T_Ptr) is
      Tmp : T := X.all;
   begin
      X.all := Y.all;
      Y.all := Tmp;
   end Swap;

end Pointers;
