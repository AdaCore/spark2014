package body P is
   procedure Shadow_Effect (D : in out Dots) is
   begin
      for C in Color loop
	 D(C) := D(C);
      end loop;
   end Shadow_Effect;


   function P (R : Repr) return Integer is
   begin
      return Repr'Pos (R);
   end P;

   function Q (R : Repr) return Integer is
   begin
      return Repr'Pos (R);
   end Q;

end P;
