package body Test is
   ----------------
   -- Equivalent --
   ----------------

   function Equivalent (A, B : Record_T) return Boolean is
   begin
      return (A.X = B.X);
   end Equivalent;
end Test;
