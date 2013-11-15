package body Levels
with Refined_State => (Abs_0 => (X0, Y0, Nested_1.Abs_1))
is

   pragma Warnings (Off, "pragma * is not yet supported");

   X0 : Integer;
   Y0 : Integer;

   function Read_Partial_0 return Integer
   with Refined_Global => X0
   is
   begin
      return X0;
   end Read_Partial_0;

   procedure Post_Test_01
   with Refined_Global => (Proof_In => (X0, Y0, Nested_1.Abs_1)),
        Refined_Post   => Wibble_0 > Read_Partial_0
   is
   begin
      null;
   end Post_Test_01;

   pragma Warnings (Off, "unused *");
   procedure Post_Test_02
   with Refined_Global => X0,
     Refined_Post   => Read_Partial_0 + 1 > X0
   is
   begin
      null;
   end Post_Test_02;
   pragma Warnings (On, "unused *");

   procedure Test_01 (A : out Integer)
   with Global => X0
   is
   begin
      A := Read_Partial_0;
   end Test_01;

   package Nested_1
   with Abstract_State => Abs_1
   is

      function Read_Partial_1 return Integer
      with Global => Abs_1;

      function Read_Partial_1_Inner return Integer
      with Global => Abs_1;

      procedure Test_11 (A : out Integer)
      with Global => (X0, Abs_1),
           Post => A = Read_Partial_0 + Read_Partial_1 + Read_Partial_1_Inner;

      procedure D_Test_02 (X : out Integer)
      with Global => (X0, Abs_1),
           Depends => (X => (X0, Abs_1));

   end Nested_1;

   procedure D_Test_01 (X : out Integer;
                        Y : in out Integer)
     with Refined_Global  => (X0, Nested_1.Abs_1),
          Refined_Depends => (X => (X0, Nested_1.Abs_1),
                              Y =>+ X0)
   is
   begin
      X := X0 + Nested_1.Read_Partial_1;
      Y := Y + X0;
   end D_Test_01;

   procedure Test_02 (A : out Integer)
   with Global => (X0, Y0, Nested_1.Abs_1)
   is
   begin
      A := Wibble_0;  -- uses X0, Y0 and Nested_1.Abs_1
   end Test_02;

   package body Nested_1
   with Refined_State => (Abs_1 => (X1, Y1, Nested_2.Abs_2))
   is

      X1 : Integer;
      Y1 : Integer;

      package Nested_2
      with
        Abstract_State => Abs_2,
        Initializes => Abs_2,
        Initial_Condition => Read_Partial_2 = 0
      is

         function Read_Partial_2 return Integer
         with Global => Abs_2;

      end Nested_2;

      package body Nested_2
      with Refined_State => (Abs_2 => (X2, Y2))
      is
         X2 : Integer := 0;
         Y2 : Integer := 0;

         function Read_Partial_2 return Integer
         with Refined_Global => X2
         is
         begin
            return X2;
         end Read_Partial_2;

      end Nested_2;

      function Read_Partial_1 return Integer
      with Refined_Global => X1
      is
      begin
         return X1;
      end Read_Partial_1;

      function Read_Partial_1_Inner return Integer
      with Refined_Global => Nested_2.Abs_2
      is
      begin
         return Nested_2.Read_Partial_2;
      end Read_Partial_1_Inner;

      procedure Test_11 (A : out Integer)
      with Refined_Global => (X0, X1, Nested_2.Abs_2),
        Refined_Post => A = Read_Partial_0 + Read_Partial_1 + Nested_2.Read_Partial_2
      is
      begin
         A := X0 + X1 + Nested_2.Read_Partial_2;
      end Test_11;

      procedure D_Test_02 (X : out Integer)
      with Refined_Global  => (X0, X1, Y1, Nested_2.Abs_2),
           Refined_Depends => (X => (X0, X1, Y1, Nested_2.Abs_2))
      is
         Tmp : Integer := 12;
      begin
         D_Test_01 (X, Tmp);
         X := X + Tmp;
      end D_Test_02;

   end Nested_1;

   procedure Test_03 (A : out Integer)
   with Refined_Global => (X0, Nested_1.Abs_1),
        Refined_Post => A = Read_Partial_0 + Nested_1.Read_Partial_1 + Nested_1.Read_Partial_1_Inner
   is
   begin
      Nested_1.Test_11 (A);
   end Test_03;

   function Read_Partial_Combined return Integer
   with Refined_Global => (X0, Nested_1.Abs_1)
   is
   begin
      return X0 + Nested_1.Read_Partial_1;
   end Read_Partial_Combined;


end Levels;
