package body Test with SPARK_Mode is

   procedure Test is
      C : C_Type := C_Type'(E => A);
   begin
      pragma Assert (if Get_E (C) = A and then Get_E (C) = B then True else True);
      if Get_E (C) = A and then Get_E (C) = B then
         pragma Assert (True = False);
      end if;
   end Test;

end Test;
