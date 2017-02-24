package P
--# own P_State : Integer;
with SPARK_Mode,
     Abstract_State => P_Abs_State
is

   function Get_P_State return Integer;

   procedure Set_Value (Value : in Integer)
   --# global out P_State;
   --# post P_State = Value;
   with Global => (Output => P_Abs_State),
        Post => Get_P_State = Value;

   function Calculate (X : Integer) return Integer
   --# global P_State;
   --# pre P_State > 0;
   with Pre => Get_P_State > 0;

private
   P_State : Integer with Part_Of => P_Abs_State;  -- Here because it is used by child packages.

   function Get_P_State return Integer is (P_State);

end P;
