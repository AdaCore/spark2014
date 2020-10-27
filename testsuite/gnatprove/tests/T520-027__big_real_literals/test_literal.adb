with Ada.Numerics.Big_Numbers.Big_Reals; use Ada.Numerics.Big_Numbers.Big_Reals;

procedure Test_Literal with
  SPARK_Mode
is

   procedure Foo_2 (Value : Big_Real) with
     Pre  => 10000000000000000000000000000000000000000000000000.0 <= Value, --@PRECONDITION:FAIL
     Ghost;

   procedure Foo_2 (Value : Big_Real)
   is
   begin
      pragma Assert (0.0 <= Value); --  Too big literals are not handled yet
   end Foo_2;

   procedure Bad (C : Integer) is
      X : Big_Real;
   begin
      case C is
      when 0 =>
         X := From_String ("toto"); --@PRECONDITION:FAIL
      when 2 =>
         X := From_String ("100"); --@PRECONDITION:FAIL
      when 3 =>
         X := From_String ("100e3e4"); --@PRECONDITION:FAIL
      when others =>
         null;
      end case;
   end Bad;

begin
   pragma Assert (Big_Real'(124.567) = (To_Big_Real (124) + To_Big_Real (567) / To_Big_Real (1000)));
   pragma Assert (Big_Real'(124.567e1) = (To_Big_Real (124) + To_Big_Real (567) / To_Big_Real (1000)) * To_Big_Real (10));
   pragma Assert (Big_Real'(124.567e-3) = (To_Big_Real (124) + To_Big_Real (567) / To_Big_Real (1000)) / To_Big_Real (1000));
   pragma Assert (Big_Real'(134.567e1) = (Big_Real'(134.0) + Big_Real'(567.0) / Big_Real'(1000.0)) * Big_Real'(10.0));
   pragma Assert (Big_Real'(134.567e-3) = (Big_Real'(134.0) + Big_Real'(567.0) / Big_Real'(1000.0)) / Big_Real'(1000.0));
end Test_Literal;
