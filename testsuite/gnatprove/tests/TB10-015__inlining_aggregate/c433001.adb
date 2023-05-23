procedure C433001 is

   type Array_3 is array (Positive range <>, Positive range <>) of Integer;

   subtype Sub_3_1 is Array_3 (1 .. 3, 4 .. 6);

   procedure Check_3 (Test_Obj : Array_3) is
   begin
      null;
   end Check_3;

begin
   Check_3 (Sub_3_1'((1, 2, 3), (2, 4, 6)));
end C433001;
