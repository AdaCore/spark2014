with Ada.Numerics.Generic_Real_Arrays;

procedure A is

   package FRA is new Ada.Numerics.Generic_Real_Arrays (Float);
   --  For the purpose of this test Generic_Real_Arrays behaves just like
   --  Generic_Elementary_Functions (which was the original subject of this TN)
   --  but does not suffer from using Long_Long_Float. See foo.adb.

   use FRA;

   X : constant Real_Vector := Unit_Vector (1,1,1);

begin
   null;
end;
