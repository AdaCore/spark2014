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

   procedure Test_02 (X :     Integer;
                      Y : out Integer)
   with
      Depends => (Y => X)
   is
      N : Integer := X;

      package P2
      with Initializes => (M => N)
      is
         M : Integer := N;
      end P2;
   begin
      Y := P2.M;
   end Test_02;

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
      Y := P3.M + X;
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

   procedure Test_05 (Z : out Boolean)
   with
      Global => null
   is
      package P5_Outer
      with Abstract_State => State
      is
         procedure Init
           with Global => (Output => State);

         function Wibble return Boolean
           with Global => State;
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

         procedure Init
           with Refined_Global => (Output => (X,
                                              P5_Inner.Y))
         is
         begin
            X          := False;
            P5_Inner.Y := False;
         end Init;

         function Wibble return Boolean
           with Refined_Global => X
         is
         begin
            return X;
         end Wibble;

      end P5_Outer;
   begin
      P5_Outer.Init;
      Z := P5_Outer.Wibble;
   end Test_05;

   procedure Test_06 (Z : out Boolean)
     with Global => null
   is
      package P6_Outer
      with Abstract_State => State,
           Initializes    => State
      is
         function Get_State return Boolean with Global => State;
      end P6_Outer;

      package body P6_Outer
        with Refined_State => (State => (X, P6_Inner.Y))
      is
         X : Boolean;

         package P6_Inner
         is
            Y : Boolean;
         end P6_Inner;

         function Get_State return Boolean
           with Refined_Global => (X, P6_Inner.Y)
         is
         begin
            return X or P6_Inner.Y;
         end Get_State;

      begin
         X          := False;
         P6_Inner.Y := False;
      end P6_Outer;
   begin
      Z := P6_Outer.Get_State;
   end Test_06;


end Flo_Review_Tests;
