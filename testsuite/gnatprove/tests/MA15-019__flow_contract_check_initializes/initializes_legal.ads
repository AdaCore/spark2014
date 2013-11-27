with Init;

package Initializes_Legal
  with SPARK_Mode,
       Abstract_State => (AS, AS2),
       Initializes    => (V,
                          W   => null,
                          X   => (Init.State, Init.A),
                          AS  => Init.State,
                          AS2 => (Init.State, Init.A))
is
   pragma Elaborate_Body (Initializes_Legal);

   W : Integer := 0;
   V : Integer := Init.Sum_All;
   X : Integer;

   function Add (X, Y : Integer) return Integer;
end Initializes_Legal;
