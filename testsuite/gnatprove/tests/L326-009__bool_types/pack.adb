package body Pack is

   procedure Do_Nothing is
   begin
      B1 := Derived_Bool (not B2);
      B2 := Boolean (not B1);
   end Do_Nothing;

end Pack;
