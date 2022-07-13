procedure Main with SPARK_Mode is

   package My_Package is

      type Power_Of_Two is (One, Two, Four, Eight, Sixteen, Thirty_Two);
      for Power_Of_Two use (One        => 1,
                            Two        => 2,
                            Four       => 4,
                            Eight      => 8,
                            Sixteen    => 16,
                            Thirty_Two => 32);

      type Idx is new Power_Of_Two;

      subtype Int is Integer range 1 .. 42;

      type Rec is record
        F : Integer := 1;
      end record;

      type Arr is array (Idx) of Rec;

      Fourty_Two : constant Int := 42;

      function Make_Array return Arr;

      package Nested is
         function Get_Sixteenth (A : Arr) return Integer;
      end Nested;

   end My_Package;

   package body My_Package is

      function Make_Array return Arr is
         A : Arr;
      begin
         for I in Idx loop
            declare
               R : constant Rec := (F => Fourty_Two);
            begin
               A (I) := R;
            end;
         end loop;
         return A;
      end Make_Array;

      package body Nested is
         function Get_Sixteenth (A : Arr) return Integer is (A (Sixteen).F);
      end Nested;

   end My_Package;

   A : constant My_Package.Arr := My_Package.Make_Array;

begin

   pragma Assert (My_Package.Fourty_Two = 42
         and then My_Package.Nested.Get_Sixteenth (A) = 1);   --  @ASSERT:FAIL

end Main;
