package body Test is

   procedure Test_01 (X : in Integer;
                      Y : in Integer;
                      Z : out Integer)
   is
      type T is new Integer range X .. Y;

      V : T := 0;
   begin
      V := T'First;
      Z := Integer (V);
   end Test_01;

end Test;
