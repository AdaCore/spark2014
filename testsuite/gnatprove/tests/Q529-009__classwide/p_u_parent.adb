package body P_U_Parent is

   overriding function Get_X0 (This : in U_Parent) return T0
     is (This.A_Parent.all.Get_X0);

   overriding procedure Set_X0 (This  : in out U_Parent;
                                Value : in     T0) is
   begin
      This.A_Parent.all.Set_X0 (Value);
   end Set_X0;

   overriding procedure Compute (This : in out U_Parent) is
   begin
      P_Parent.Compute (This => T_Parent'Class (This.A_Parent.all));
   end Compute;

   function Constructor (A_Parent : access T_Parent'Class) return U_Parent is
     (U_Parent'(A_Parent => A_Parent));

end P_U_Parent;
