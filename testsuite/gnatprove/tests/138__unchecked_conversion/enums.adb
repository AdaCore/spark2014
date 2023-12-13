with Ada.Unchecked_Conversion;

procedure Enums is

   type U32 is mod 2**32;
   type U4 is mod 2**4 with Size => 4;
   type U2 is mod 2**2 with Size => 2;

   type E2 is (One, Two, Three, Four) with Size => 2;
   type E2Arr is array (1 .. 2) of E2 with Pack, Size => 4;

   function To_E2 is new Ada.Unchecked_Conversion (Source => U2, Target => E2);
   function Of_E2 is new Ada.Unchecked_Conversion (Source => E2, Target => U2);

   function To_E2Arr is new Ada.Unchecked_Conversion (Source => U4, Target => E2Arr);
   function Of_E2Arr is new Ada.Unchecked_Conversion (Source => E2Arr, Target => U4);

   procedure Test_E2 (X : U2; Y : E2)
     with Global => null
   is
      Conv_X : constant E2 := To_E2 (X);
      Conv_Y : constant U2 := Of_E2 (Y);
   begin
      pragma Assert (Of_E2 (Conv_X) = X);

      pragma Assert (To_E2 (Conv_Y) = Y);
   end;

   procedure Test_E2Arr (X : U4; Y : E2Arr)
     with Global => null
   is
      Conv_X : constant E2Arr := To_E2Arr (X);
      Conv_Y : constant U4 := Of_E2Arr (Y);
   begin
      pragma Assert (Of_E2Arr (Conv_X) = X);

      pragma Assert (To_E2Arr (Conv_Y) = Y);
   end;

   -----

   type Barr is array (Positive range <>) of Boolean with Pack;
   subtype B32 is Barr(1 .. 32);

   function To_B32 is new Ada.Unchecked_Conversion (Source => U32, Target => B32);
   function Of_B32 is new Ada.Unchecked_Conversion (Source => B32, Target => U32);

   procedure Test_B32 (X : U32; Y : B32)
     with Global => null
   is
      Conv_X : constant B32 := To_B32 (X);
      Conv_Y : constant U32 := Of_B32 (Y);
   begin
      pragma Assert (Of_B32 (Conv_X) = X);

      pragma Assert (To_B32 (Conv_Y) = Y);
   end;

begin
   Test_E2 (0, One);
   Test_E2Arr (0, E2Arr'(others => One));
   Test_B32 (0, B32'(others => True));
end;
