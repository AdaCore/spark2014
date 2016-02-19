with Base.A.B;

package body Base.A with
   Refined_State => (State        => Base.A.B.State,
                     Atomic_State => Base.A.B.Atomic_State),
   SPARK_Mode
is
end Base.A;
