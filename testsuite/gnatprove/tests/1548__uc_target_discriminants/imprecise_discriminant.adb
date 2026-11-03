with Ada.Unchecked_Conversion;

procedure Imprecise_Discriminant with SPARK_Mode is
   type Byte is mod 2 ** 8 with Size => 8;
   type Bytes is array (Positive range <>) of Byte
     with Component_Size => 8;
   type Raw is new Bytes (1 .. 32) with Alignment => 4;
   subtype Padding is Bytes (1 .. 24);
   type Rec (D : Natural) is record
      Value : Natural;
      Pad   : Padding;
   end record with Size => 256;
   for Rec use record
      D     at 0 range 0 .. 31;
      Value at 4 range 0 .. 31;
      Pad   at 8 range 0 .. 191;
   end record;
   subtype Fixed is Rec (0);
   function Convert is new Ada.Unchecked_Conversion (Raw, Fixed) --@UNCHECKED_CONVERSION:FAIL
     with Potentially_Invalid;

   procedure Inspect (X : Rec) with
     Pre => True,
     Potentially_Invalid => X
   is
   begin
      pragma Assert (X.D >= 0);
   end Inspect;

   Input : Raw := (1 .. 4 => 255, others => 0);
   X : Fixed := Convert (Input) with Potentially_Invalid;
begin
   Inspect (X);
end Imprecise_Discriminant;
