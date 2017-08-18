package body Sc_Status_Type is

   procedure Check (This : Object_Type) is
   begin
      pragma Assert (This.Sc_State.Prime = This.Sc_State.Shadow);
   end Check;

end Sc_Status_Type;
