package body Parent.Child
   with Refined_State => (Child_State => X)
is

   X : Integer;
   procedure P is
   begin
      X := 0;
   end P;

end Parent.Child;
