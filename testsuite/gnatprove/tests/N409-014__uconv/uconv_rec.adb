with Ada.Unchecked_Conversion; use Ada;

procedure Uconv_Rec with
  SPARK_Mode
is

   type Rec1 is record X, Y : Integer; end record;
   type Rec2 is new Rec1;

   function To_Rec2 is new Unchecked_Conversion (Rec1, Rec2);

   X : Rec1 := (others => 0);
   Y : Rec2;
begin
   Y := To_Rec2 (X);
end Uconv_Rec;
