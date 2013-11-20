pragma SPARK_Mode (On);
package Loop_Entry
is

  subtype ElementType is Natural range 0..1000;
  subtype IndexType is Positive range 1..100;
  type ArrayType is array (IndexType) of ElementType;

   procedure Clear (A: in out ArrayType; L,U: in IndexType)
     with Depends => (A => (A, L, U)),
          Post    => (for all N in L..U => A(N) = 0) and
                     (for all N in IndexType =>
                         (if N<L or N>U then A(N) = A'Old(N)));

end Loop_Entry;
