package body IC
with Refined_State => (State_A => (Test_01.X,
                                   Test_02.X,
                                   Test_03.X,
                                   Test_04.X),
                       State_B => (Test_01.Y,
                                   Test_02.Y,
                                   Test_03.Y,
                                   Test_04.Y,
                                   Test_06.S))
is
   package Test_01
     with Initializes => X,
          Initial_Condition => X > 0
   is
      X : Integer;
      Y : Integer;

      function Get_Stuff return Integer is (X + Y);
   end Test_01;

   package body Test_01
   is
   begin
      X := 5;
   end Test_01;

   package Test_02
     with Initializes => X,
          Initial_Condition => X = Y  --  use of uninitialized variable
   is
      X : Integer;
      Y : Integer;
   end Test_02;

   package body Test_02
   is
   begin
      X := 5;
   end Test_02;

   package Test_03
     with Initializes => (X => Test_01.X),
          Initial_Condition => X = Test_01.X
   is
      X : Integer;
      Y : Integer;
   end Test_03;

   package body Test_03
   is
   begin
      X := Test_01.X;
   end Test_03;

   package Test_04
     with Initializes => (X => Test_01.X),
          Initial_Condition => X = Test_01.Get_Stuff  -- y not visible
   is
      X : Integer;
      Y : Integer;
   end Test_04;

   package body Test_04
   is
   begin
      X := Test_01.X;
   end Test_04;

   package Test_05
   with
     Initializes => null,
     Initial_Condition => Test_01.Get_Stuff > 0  --  x, y not visible
   is
   end Test_05;

   package body Test_05
   is
   end Test_05;

   package Test_06 with
     Abstract_State => S
   is
      procedure Sanity_Check_5 with
        Global => (In_Out => S),
        Post   => True;
   end Test_06;

   package body Test_06 with
     Refined_State => (S => (X, Y))
   is
      X : Integer;
      Y : Integer;

      procedure Sanity_Check_5 with
        Refined_Global => (Output => X),
        Refined_Post   => X = Y               --  y is not visible
      is
      begin
         X := 12;
      end Sanity_Check_5;

   end Test_06;


   procedure Sanity_Check_1 with
     Global => (Output => Test_01.X),
     Post   => Test_01.X = Test_02.Y   -- y not visible
   is
   begin
      Test_01.X := 0;
   end Sanity_Check_1;

   procedure Sanity_Check_2 (B : Boolean) with
     Global => (Output => Test_01.X),
     Contract_Cases => (B     => Test_01.X > 0,
                        not B => Test_01.Y > 0)  -- y not visible
   is
      pragma Unreferenced (B);
   begin
      Test_01.X := 0;
   end Sanity_Check_2;

   procedure Sanity_Check_3 with
     Post => Test_01.X = Test_02.Y   -- ok, because y is visible
   is
   begin
      Test_01.X := 0;
   end Sanity_Check_3;

   procedure Sanity_Check_4 (B : Boolean) with
     Contract_Cases => (B     => Test_01.X > 0,
                        not B => Test_01.Y > 0)  -- ok, because y is visible
   is
      pragma Unreferenced (B);
   begin
      Test_01.X := 0;
   end Sanity_Check_4;

end IC;
