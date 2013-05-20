package body Test
is

   Z : Integer;

   procedure Test_01 (X : Integer; -- Unused
                      Y : out Integer)
   with Global  => null,
        Depends => (Y => null,
                    null => X)
   is
   begin
      Y := 0;
   end Test_01;

   procedure Test_02 (X : Integer; -- Ineffective
                      Y : out Integer)
   is
   begin
      Test_01 (X, Y);
   end Test_02;

   procedure Test_03 (Y : out Integer)
   with Global  => Z, -- unused
        Depends => (Y => null,
                    null => Z)
   is
   begin
      Y := 0;
   end Test_03;

   procedure Test_04 (Y : out Integer)
   with Global  => Z -- ineffective
   is
   begin
      Test_03 (Y);
   end Test_04;

end Test;
