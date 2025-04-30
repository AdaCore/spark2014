procedure Test_Numeric_Trait with SPARK_Mode is
   function Random return Integer with Import, Global => null;
   package Num is
      type I is mod 257;
      type Numeric is tagged record
         Field : I;
      end record;
      function Zero return Numeric is (Field => 0);
      function One return Numeric is (Field => 1);
      function Add (X, Y : Numeric) return Numeric is
         (Field => X.Field + Y.Field);
      function Mul (X, Y : Numeric) return Numeric is
         (Field => X.Field * Y.Field);
      function Equal (X, Y : Numeric) return Boolean is (X.Field = Y.Field);
      function On_Unit_Circle (X, Y : Numeric) return Boolean
        with
          Import,
          Global => null,
          Post'Class =>
            On_Unit_Circle'Result = Equal (One, Add (Mul (X, X), Mul (Y, Y)));
      function Imaginary return Numeric
        with
          Import,
          Global => null,
          Post'Class =>
            Equal (Zero, Add (Mul (Imaginary'Result, Imaginary'Result), One));
   end Num;
   use Num;
   X : Numeric'Class := Numeric'(Field => 3);
   Y : Numeric'Class := Numeric'(Field => 4);
   Z : Numeric'Class := Numeric'(Field => 0);
   T : Numeric'Class := Numeric'(Field => 16);
begin
   case Random is
      when 0 =>
         pragma Assert (On_Unit_Circle (X, Y)); --@ASSERT:FAIL
      when 1 =>
         pragma Assert (Equal (Z, Add (Mul (Imaginary, Imaginary), One)));
      when 2 =>
         pragma Assert (On_Unit_Circle (T, One));
      when others => null;
   end case;
end Test_Numeric_Trait;
