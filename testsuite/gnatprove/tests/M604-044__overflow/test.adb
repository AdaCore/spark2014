package body Test
is
   function Range_Check_Error (A : in Enum_T) return Enum_T
   is
   begin
      pragma Assert (Enum_T'Succ (A) > A or True);
      return A;
   end Range_Check_Error;
end Test;
