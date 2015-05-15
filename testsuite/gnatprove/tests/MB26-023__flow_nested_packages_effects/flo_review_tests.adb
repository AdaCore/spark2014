package body Flo_Review_Tests is

   --  This is correct and should raise no errors or warnings.
   procedure Test_01 (X :     Integer;
                      Y : out Integer)
   with
      Global => null,
      Depends => (Y => X)
   is
      N : Integer := X;

      package P1
      with Initializes => (M => N)
      is
         M : Integer := N;
      end P1;
   begin
      Y := P1.M;
   end Test_01;

end Flo_Review_Tests;
