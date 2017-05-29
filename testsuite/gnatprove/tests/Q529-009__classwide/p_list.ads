with P_U_Parent; use P_U_Parent;

package P_List
with SPARK_Mode
is

   type T_Index is range 0 .. 2;

   type T_List is array (T_Index) of U_Parent;

   function Init return T_List
   with Global => null;

end P_List;
