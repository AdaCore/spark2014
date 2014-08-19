package body Dic3 is
   function To_Int (R : Root_T) return Integer is (Integer (R));

   function To_Int (D : Derived_T) return Integer is (Integer (D));

   procedure Test is
      X : Root_T;
      Y : Derived_T;
   begin
      pragma Assert (Integer (X) = Integer (Y));
   end Test;
end Dic3;
