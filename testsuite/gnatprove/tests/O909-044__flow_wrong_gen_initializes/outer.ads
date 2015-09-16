with Helper; use Helper;

package Outer with SPARK_Mode,
   Abstract_State => Out_State
is
   pragma Elaborate_Body;
private
   package Inner with
     Abstract_State => (In_State with Part_Of => Out_State)
   is
      type Buffer is private;
   private
      Priv : Natural := Var with Part_Of => In_State;
      type Buffer is null record;
   end Inner;
end Outer;
