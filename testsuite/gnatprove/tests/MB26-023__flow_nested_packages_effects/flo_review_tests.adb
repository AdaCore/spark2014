package body Flo_Review_Tests
is

   --  This is correct and should raise no errors or warnings.
   procedure Test_01 (X :     Integer;
                      Y : out Integer)
   with
      Global => null,
      Depends => (Y => X)
   is
      N : Integer := X;

      package P
      with Initializes => (M => N)
      is
         M : Integer := N;
      end P;
   begin
      Y := P.M;
   end Test_01;

   --  This is correct and should raise no errors or warnings.
   --  This should be fixed/enabled once M523-040 is implemented.
   --  procedure Test_02 (X :     Integer;
   --                     Y : out Integer)
   --  with
   --     Depends => (Y => X)
   --  is
   --     N : Integer := X;

   --     package P
   --     with Initializes => (M => N)
   --     is
   --        M : Integer := N;
   --     end P;
   --  begin
   --     Y := P.M;
   --  end Test_02;

end Flo_Review_Tests;
