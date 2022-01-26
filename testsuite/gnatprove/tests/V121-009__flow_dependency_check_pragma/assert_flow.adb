procedure Assert_Flow (X, Y : Positive) with SPARK_Mode is

   procedure Test with Global => (Proof_In => (X,Y)) is
      --  Global contract is correct
      --  X and Y are used in the default initialisations of
      --  T_Arr and U_Arr respectively in the assertions below.
      type T (D : Positive) is record
         C : Integer := D - 1;
      end record;

      type U is record
         C : Integer := Y - 1;
      end record;

      type T_Arr is array (Positive range <>) of T (X);
      type U_Arr is array (Positive range <>) of U;
   begin
      pragma Assert (T_Arr'(1 .. 5 => <>) (1).C = -1);
      pragma Assert (U_Arr'(1 .. 5 => <>) (1).C = -1);
      --  Assertions deliberately intended to fail
   end;

begin
   Test;
end Assert_Flow;
