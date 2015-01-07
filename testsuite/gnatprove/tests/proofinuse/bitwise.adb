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

   procedure Write16 (Val : in Unsigned_16; FstHalf, SndHalf : out Unsigned_8) is
   begin
      FstHalf := Unsigned_8 (Val and 16#00FF#);
      SndHalf := Unsigned_8 (Shift_Right(Val, 8) and 16#00FF#);
      pragma assert (Val =
                     (Unsigned_16(FstHalf) or
                          Shift_Left(Unsigned_16(SndHalf), 8 )));
   end Write16;

   procedure Read32 (Val1, Val2, Val3, Val4 : in Unsigned_8; Res : out Unsigned_32) is
   begin
      Res := (Unsigned_32(Val1) or
                Shift_Left(Unsigned_32(Val2), 8) or
                  Shift_Left(Unsigned_32(Val3), 16) or
                Shift_Left(Unsigned_32(Val4), 24));
      pragma assert (Res =
                     (Unsigned_32(
                        Unsigned_16(Val1) or Shift_Left(Unsigned_16(Val2), 8)
                       ) or Shift_Left(Unsigned_32(
                          Unsigned_16(Val3) or Shift_Left(Unsigned_16(Val4), 8)
                         ), 16)));
   end Read32;

end Bitwise;
