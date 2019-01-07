pragma SPARK_Mode;
package body Pointers is

   procedure Swap (X, Y : T_Ptr) is
      Tmp : T := X.all;
   begin
      X.all := Y.all;
      Y.all := Tmp;
   end Swap;

   procedure Swap (R : T_Rec) is
   begin
      Swap (R.A, R.B);
   end Swap;

end Pointers;
