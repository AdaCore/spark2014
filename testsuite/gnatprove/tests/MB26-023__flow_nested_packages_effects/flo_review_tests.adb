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

      package P1
      with Initializes => (M => N)
      is
         M : Integer := N;
      end P1;
   begin
      Y := P1.M;
   end Test_01;

   --  This is correct and should raise no errors or warnings.
   --  This should be fixed/enabled once M523-040 is implemented.
   --  procedure Test_02 (X :     Integer;
   --                     Y : out Integer)
   --  with
   --     Depends => (Y => X)
   --  is
   --     N : Integer := X;

   --     package P2
   --     with Initializes => (M => N)
   --     is
   --        M : Integer := N;
   --     end P2;
   --  begin
   --     Y := P2.M;
   --  end Test_02;

   procedure Test_03 (X :     Integer;
                      Y : out Integer)
   with
      Global => null,
      Depends => (Y => X)
   is
      N : Integer;

      package P3
      with Initializes => (M => N)  -- error
      is
         M : Integer := N;
      end P3;
   begin
      Y := X;
   end Test_03;

   procedure Test_04
   with
      Global => null
   is
      package P4
      with Initializes => M  -- unhelpful error here
      is
         M : Integer := 0;   -- unused (but no error)
         N : Integer;        -- unused
      end P4;
   begin
      null;
   end Test_04;

   procedure Test_05 (X : out Integer)
   with
      Global => null
   is
      package P5_Outer
      with Abstract_State => State
      is
      end P5_Outer;

      package body P5_Outer
      with Refined_State => (State => (X, P5_Inner.Y))
      is
         X : Boolean;

         package P5_Inner
         with Initializes => Y
         is
            Y : Boolean;  -- Uninitialized!
         end P5_Inner;

      end P5_Outer;
   begin
      null;
   end Test_05;


end Flo_Review_Tests;
