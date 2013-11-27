with Init;

package Initializes_Illegal
  with SPARK_Mode,
       Abstract_State => SA,
       Initializes    => (V  => null,
                          X  => (Init.State, Init.A),
                          SA => Init.State)
is
   V : Integer := Init.A;          --  warning: V must not depend on A
   W : Integer := 0;               --  warning: initialization has no effect
   X : Integer := Init.Sum_State;  --  warning: X does not depend on A

   procedure Does_Nothing;
end Initializes_Illegal;
