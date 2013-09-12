package body A is
   pragma SPARK_Mode (Off);  --  conversion between composite
   procedure K is
      X : D := (A => 1, B => 2);
      Y : T := T (X);
      Z : D := D (Y);
   begin
      null;
   end K;
end A;
