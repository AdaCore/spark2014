with Types; use Types;
with P_Parent; use P_Parent;

package P_Heir2
with SPARK_Mode
is pragma Elaborate_Body;

   type T_Heir2 is new T_Parent with private;

   function Get_X2 (This : in T_Heir2) return T2;

   procedure Set_X2 (This  : in out T_Heir2;
                     Value : in     T2);

   overriding procedure Compute (This : in out T_Heir2);

private

   type T_Heir2 is new T_Parent with record
      X2 : T2;
   end record;

end P_Heir2;
