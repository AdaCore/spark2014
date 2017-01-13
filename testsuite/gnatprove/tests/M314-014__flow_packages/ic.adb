package body IC
with Refined_State => (State_A => (Test_01.X01,
                                   Test_02.X02,
                                   Test_03.X03,
                                   Test_04.X04),
                       State_B => (Test_01.Y01,
                                   Test_02.Y02,
                                   Test_03.Y03,
                                   Test_04.Y04,
                                   Test_06.S))
is
   package Test_01
     with Initializes => X01,
          Initial_Condition => X01 > 0
   is
      X01 : Integer;
      Y01 : Integer;

      function Get_Stuff return Integer;
   end Test_01;

   package Test_02
     with Initializes => X02,
          Initial_Condition => X02 = Y02  --  use of uninitialized variable
   is
      X02 : Integer;
      Y02 : Integer;
   end Test_02;

   package Test_03
     with Initializes => (X03 => Test_01.X01),
          Initial_Condition => X03 = Test_01.X01
   is
      X03 : Integer;
      Y03 : Integer;
   end Test_03;

   package Test_04
     with Initializes => (X04 => Test_01.X01),
          Initial_Condition => X04 = Test_01.Get_Stuff  -- y not visible
   is
      X04 : Integer;
      Y04 : Integer;
   end Test_04;

   package Test_05
   with
     Initializes => null,
     Initial_Condition => Test_01.Get_Stuff > 0  --  x, y not visible
   is
   end Test_05;

   package Test_06 with
     Abstract_State => S
   is
      procedure Sanity_Check_5 with
        Global => (In_Out => S),
        Post   => True;
   end Test_06;

   package body Test_03
   is
   begin
      X03 := Test_01.X01;
   end Test_03;

   package body Test_02
   is
   begin
      X02 := 5;
   end Test_02;

   package body Test_04
   is
   begin
      X04 := Test_01.X01;
   end Test_04;

   package body Test_05
   is
   end Test_05;

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

   package body Test_01
   is
      function Get_Stuff return Integer is (X01 + Y01);
   begin
      X01 := 5;
   end Test_01;


   procedure Sanity_Check_1 with
     Global => (Output => Test_01.X01),
     Post   => Test_01.X01 = Test_02.Y02   -- y not visible
   is
   begin
      Test_01.X01 := 0;
   end Sanity_Check_1;

   procedure Sanity_Check_2 (B : Boolean) with
     Global => (Output => Test_01.X01),
     Contract_Cases => (B     => Test_01.X01 > 0,
                        not B => Test_01.Y01 > 0)  -- y not visible
   is
      pragma Unreferenced (B);
   begin
      Test_01.X01 := 0;
   end Sanity_Check_2;

   procedure Sanity_Check_3 with
     Post => Test_01.X01 = Test_02.Y02   -- ok, because y is visible
   is
   begin
      Test_01.X01 := 0;
   end Sanity_Check_3;

   procedure Sanity_Check_4 (B : Boolean) with
     Contract_Cases => (B     => Test_01.X01 > 0,
                        not B => Test_01.Y01 > 0)  -- ok, because y is visible
   is
      pragma Unreferenced (B);
   begin
      Test_01.X01 := 0;
   end Sanity_Check_4;

end IC;
