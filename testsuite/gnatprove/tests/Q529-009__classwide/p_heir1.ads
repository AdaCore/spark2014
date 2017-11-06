with Types; use Types;
with P_Parent; use P_Parent;

package P_Heir1
with SPARK_Mode
is pragma Elaborate_Body;

   type T_Heir1 is new T_Parent with private;

   function Get_X1 (This : in T_Heir1) return T1;

   procedure Set_X1 (This  : in out T_Heir1;
                     Value : in     T1);

   overriding procedure Compute (This : in out T_Heir1);

private

   type T_Heir1 is new T_Parent with record
      X1 : T1;
   end record;

end P_Heir1;
