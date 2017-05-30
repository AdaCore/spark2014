with B.Priv;

package body B with
   Refined_State => (State        => (Priv.State, Flag_1),
                     Atomic_State => (Priv.Atomic_State, Flag_2))
is

   Flag_1 : Boolean;
   Flag_2 : Boolean with Volatile, Atomic, Async_Writers;

   procedure Read_State (X : out Boolean)
   is
   begin
      Priv.P_Read_State (X);
      X := X xor Flag_1;
   end Read_State;

   procedure Read_Atomic_State (X : out Boolean)
   is
      Tmp : constant Boolean := Flag_2;
   begin
      Priv.P_Read_Atomic_State (X);
      X := X xor Tmp;
   end Read_Atomic_State;

end B;
