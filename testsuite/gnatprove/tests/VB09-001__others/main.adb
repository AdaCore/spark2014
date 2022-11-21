procedure Main
  with
    SPARK_Mode => On
is

    type Color_Type is (Red, Orange, Yellow, Green, Blue, Indigo, Violet);

    type Array_3 is array (Color_Type range <>, Positive range <>) of Integer;

    subtype Sub_3_1 is Array_3 (Red .. Yellow, 3 .. 5);

    X : Array_3 := Sub_3_1'((1, others => 3), others => (2, 4, others => 6));
begin
   pragma Assert (X (Red, 3) = 1);
   pragma Assert (X (Red, 4) = 3);
   pragma Assert (X (Red, 5) = 3);
   pragma Assert (X (Orange, 3) = 2);
   pragma Assert (X (Orange, 4) = 4);
   pragma Assert (X (Orange, 5) = 6);
   pragma Assert (X (Yellow, 3) = 2);
   pragma Assert (X (Yellow, 4) = 4);
   pragma Assert (X (Yellow, 5) /= 6); --@ASSERT:FAIL
end Main;
