package body Test
with
   Refined_State => (State => T)
is

   procedure Inc
   --  NOTE: with the explicit contract below, the error goes away
   --  with
   --     Refined_Global => (In_Out => T, Input => Values.Val)
   is
   begin
      T := T + Prop.Get_Val;
   end Inc;

end Test;
