with Types; use Types;

package P_I_Parent
with SPARK_Mode
is

   type I_Parent is interface;

   function Get_X0 (This : in I_Parent) return T0 is abstract;

   procedure Set_X0 (This  : in out I_Parent;
                     Value : in     T0) is abstract;

   procedure Compute (This : in out I_Parent) is abstract;

end P_I_Parent;
