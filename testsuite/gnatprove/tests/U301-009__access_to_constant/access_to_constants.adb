package body Access_To_Constants with SPARK_Mode is

   function Allocate_Int_Acc (X : Integer) return Int_Acc with
     SPARK_Mode => Off
   is
      Y : constant Int_Acc := new Integer'(X);
   begin
      return Y;
   end Allocate_Int_Acc;

   function Allocate_Int_Acc (X : Integer) return Rec
   is
      Y : constant Int_Acc := new Integer'(X);
   begin
      return (F => Y);
   end Allocate_Int_Acc;

   Y_3 : constant C_Rec_Acc := new Rec'(F => Allocate_Int_Acc (15));  -- should be ok
   X_4 : constant Rec := Allocate_Int_Acc (15);
   Y_4 : constant C_Rec_Acc := new Rec'(X_4); -- should be ok
   X_5 : constant Rec := Allocate_Int_Acc (15);
   Y_5 : constant C_Int_Acc := C_Int_Acc (X_4.F); -- should be ok

begin
   X.all := 14; --  X has been moved
   Z.all := 14; --  Z has been moved
end Access_To_Constants;
