with ASM_Stack;
with ADT_Stack;

package Random_Numbers with
  SPARK_Mode,
  Abstract_State => State,
  Initializes => State
is
   procedure Random (Res : out Integer);
   function GCD (M, N : Integer) return Integer;
end Random_Numbers;
