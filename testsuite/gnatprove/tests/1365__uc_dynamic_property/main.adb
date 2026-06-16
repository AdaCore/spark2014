with Ada.Unchecked_Conversion;
procedure Main with SPARK_Mode is

   --  Check that the result of an UC is known to be in the bounds of its type

   type I is new Integer with Size => 32;
   function Id (X : I) return I is (X);
   subtype S is I range Id (1) .. Id (2);

   function Conv is new Ada.Unchecked_Conversion
     (Float, S);
   X : Float := 0.0;
begin
   pragma Assert (Conv (X) in 1 .. 2); -- @ASSERT:PASS
end Main;
