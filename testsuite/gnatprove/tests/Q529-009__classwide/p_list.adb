with P_Parent; use P_Parent;
with P_Heir1; use P_Heir1;
with P_Heir2; use P_Heir2;

package body P_List
with SPARK_Mode => Off
is

   Parent : aliased T_Parent;
   Parent0 : constant U_Parent := Constructor (A_Parent => Parent'Access);

   Heir1 : aliased T_Heir1;
   Parent1 : constant U_Parent := Constructor (A_Parent => Heir1'Access);

   Heir2 : aliased T_Heir2;
   Parent2 : constant U_Parent := Constructor (A_Parent => Heir2'Access);

   function Init return T_List is
     (T_List'(0 => Parent0,
              1 => Parent1,
              2 => Parent2));

end P_List;
