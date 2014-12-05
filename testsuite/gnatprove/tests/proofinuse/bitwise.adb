package body Bitwise with
  SPARK_Mode
is
   procedure Mask (X : Unsigned_32; Res : out Unsigned_8) is
   begin
      Res := Unsigned_8(((X and 16#FFFFFF00#) or 1) and 16#000000FF#);
      pragma Assert (Res = 1);
   end Mask;

   procedure Mask_8bits (X : in Unsigned_32; Res : out Unsigned_32) is
      LMask_8 : constant Unsigned_8 := 2**8 - 1;
   begin
      Res := Unsigned_32(LMask_8);
      pragma Assert ((X and Res) = (X and Unsigned_32(LMask_8)));
   end Mask_8bits;

   procedure Shift_Is_Div (X : Unsigned_32; Res : out Unsigned_32) is
   begin
      Res := Shift_Right (X, 1);
      pragma Assert (Res = X / 2);  --  shift translated as div, proved
      Res := Shift_Right (Res, 2);
      pragma Assert (Res = X / 8);  --  shift translated as div, proved by CVC4 and not proved by Alt-Ergo
   end Shift_Is_Div;

   procedure Swap (X, Y : in out Unsigned_32) is
      XX : constant Unsigned_32 := X;
      YY : constant Unsigned_32 := Y;
   begin
      X := X xor Y;
      Y := X xor Y;
      X := X xor Y;
      pragma Assert (X = YY);
      pragma Assert (Y = XX);
   end Swap;

end Bitwise;
