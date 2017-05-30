package body B.Priv with
   Refined_State => (State        => (Flag_3),
                     Atomic_State => (Flag_4))
is

   Flag_3 : Boolean;
   Flag_4 : Boolean with Volatile, Atomic;

   procedure P_Read_State (X : out Boolean)
   is
   begin
      X := Flag_3;
   end P_Read_State;

   procedure P_Read_Atomic_State (X : out Boolean)
   is
   begin
      X := Flag_4;
   end P_Read_Atomic_State;

end B.Priv;
