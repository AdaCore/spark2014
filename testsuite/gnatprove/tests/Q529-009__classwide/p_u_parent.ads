with Types; use Types;
with P_I_Parent; use P_I_Parent;
with P_Parent; use P_Parent;

package P_U_Parent
with SPARK_Mode
is

   type U_Parent is new I_Parent with private;

   overriding function Get_X0 (This : in U_Parent) return T0;

   overriding procedure Set_X0 (This  : in out U_Parent;
                                Value : in     T0);

   overriding procedure Compute (This : in out U_Parent);

   function Constructor (A_Parent : access T_Parent'Class) return U_Parent
   with SPARK_Mode => Off;

private

   pragma SPARK_Mode (Off);

   type U_Parent is new I_Parent with record
      A_Parent : not null access T_Parent;
   end record;

end P_U_Parent;
