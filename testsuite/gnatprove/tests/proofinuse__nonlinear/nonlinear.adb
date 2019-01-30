package body Nonlinear with
  SPARK_Mode
is

   procedure Scale (X, Y, Z : Natural_32; Res : out Natural_32) is
   begin
      pragma Assume (X <= Y);
      pragma Assume (Y < Z);
      pragma Assume (Y < 2 ** 15);
      Res := (X * Y) / Z;
      pragma Assert (Res <= X);
   end Scale;

   procedure Unsigned_Scale (X, Y, Z : Unsigned_32; Res : out Unsigned_32) is
   begin
      pragma Assume (X <= Y);
      pragma Assume (Y < Z);
      pragma Assume (Y < 2 ** 16);
      Res := (X * Y) / Z;
      pragma Assert (Res <= X);
   end Unsigned_Scale;

   procedure Divide (X, Y : Positive_32; Res : out Positive_32) is
   begin
      pragma Assume (X >= Y);
      Res := X / Y;
      pragma Assert ((Res * Y) / Res = Y);
   end Divide;

   procedure Power (X : Natural) is
   begin
      pragma Assume (X in 2 .. 29);
      pragma Assert (2 ** X + 2 ** (X-1) < 2 ** (X+1));
   end Power;

   procedure Mult (X, Y : Integer; Res : out Integer) is
   begin
      pragma Assume (X in -10 .. -1 and Y in 1 .. 10);
      Res := X * Y + 1;
      pragma Assert (Res in -99 .. -Y + 1);
   end Mult;

   procedure Mult_Protect (X, Y, Z : Natural_32; Res : out Integer_32) is
   begin
      pragma Assume (Y = 0 or else X <= Z / Y);
      Res := X * Y;
      pragma Assert (Res <= Z);
   end Mult_Protect;

end Nonlinear;
