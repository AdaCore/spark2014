package body Global_And_Generics is

   package body G is
      procedure P (Y : in out Integer) is
      begin
         Y := Integer'Max (X, Y);
      end P;
   end G;

   package I is new G
     (X => 123); -- actual parameter lacks variable inputs

   -- Q's Global and Depends aspects don't mention I.X even though
   -- Q calls I.P which does reference I.X as a global.
   -- As seen from outside of I, I.P's references to I.X in its
   -- Global and Depends aspect specifications are ignored.
   procedure Q (Z : in out Integer) is
   begin
      I.P (Y => Z);
   end Q;

end Global_And_Generics;
