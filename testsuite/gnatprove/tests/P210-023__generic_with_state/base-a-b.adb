with GP;

pragma Elaborate_All (GP);

package body Base.A.B with
   Refined_State =>
     (State        => (G1, C.State),
      Atomic_State => C.Atomic_State)
is

   G1 : Boolean := False;

   package C is new GP (T => Boolean);

end Base.A.B;
