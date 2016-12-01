pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

package Abstract_State_Part_Of_Concurrent with SPARK_Mode is
   protected P is
      function Get return Integer;
      procedure Set (V : Integer);
   end P;

   package P_State with Abstract_State => (State with Part_Of => P) is
      function Get_Value return Integer;
      procedure Set_Value (V : Integer);
   end P_State;

   task T;

   package T_State with Abstract_State => (State with Part_Of => T) is
      function Get_Value return Integer;
      procedure Set_Value (V : Integer);
   end T_State;

end Abstract_State_Part_Of_Concurrent;
