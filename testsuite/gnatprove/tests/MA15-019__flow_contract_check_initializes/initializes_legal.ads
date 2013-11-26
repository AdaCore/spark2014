with Init;

package Initializes_Legal
  with SPARK_Mode,
       Abstract_State => AS,
       Initializes    => (V,
                          W  => null,
                          X  => (Init.State, Init.A),
                          AS => Init.State)
is
   W    : Integer := 0;
   V, X : Integer := Init.Sum_All;
   procedure Does_Nothing;
end Initializes_Legal;
