with Types; use Types;

package P_Parent
with SPARK_Mode
is

   type T_Parent is tagged private;

   function Get_X0 (This : in T_Parent) return T0;

   procedure Set_X0 (This  : in out T_Parent;
                     Value : in     T0);

   procedure Compute (This : in out T_Parent);

private

   type T_Parent is tagged record
      X0 : T0;
   end record;

end P_Parent;
