package body Better_Error_Locations is
   procedure P (X : out Integer) is
   begin
      X := A.Return_State + B.Return_State;
   end P;
end Better_Error_Locations;
