with Interfaces;
use Interfaces;

package body Counter_Example_Loop_Index
with SPARK_Mode
is

   procedure P is
      J : Natural := 0;
      K : Natural := 0;
   begin
      for I in 1 .. 100 loop
         K := I;
         pragma Loop_Invariant (J = 0); --@LOOP_INVARIANT_PRESERV:FAIL @COUNTEREXAMPLE
         J := I;
      end loop;
   end P;

   procedure P1 is
      J : Natural := 0;
      K : Natural := 0;
   begin
     for I in 1 .. 100 loop
         pragma Loop_Invariant (True);
         pragma Loop_Invariant (J <= 50); --@LOOP_INVARIANT_PRESERV:FAIL @COUNTEREXAMPLE
         pragma Loop_Invariant (True);
         K := I;
         J := I;
      end loop;
   end P1;

   function F (X : Integer) return Boolean with
     Pre => X < 50;

   function F (X : Integer) return Boolean is
   begin
      return True;
   end F;

   --  For a RTE in the invariant
   procedure P2 is
      J : Natural := 0;
      K : Natural := 0;
   begin
      for I in 1 .. 100 loop
         pragma Loop_Invariant (True);
         pragma Loop_Invariant (F (J)); --@PRECONDITION:FAIL @COUNTEREXAMPLE
         pragma Loop_Invariant (True);
         K := I;
         J := I;
      end loop;
   end P2;

   -- With Invariants Elsewhere in The loop
   procedure P3 (X : Integer) is
      J : Natural := 0;
      K : Natural := 0;
   begin
      for I in 1 .. 100 loop
         K := I;
         pragma Loop_Invariant (J <= 50); --@LOOP_INVARIANT_PRESERV:FAIL @COUNTEREXAMPLE
         J := I;
      end loop;
   end P3;

-- With invariants at the end of the loop, I would advise to special case to put the "previous iteration" at the beginning instead of at the end of the loop:
   procedure P4 is
      J : Natural := 0;
      K : Natural := 0;
   begin
      for I in 1 .. 100 loop
         K := I;
         J := I;
         pragma Loop_Invariant (J <= 50); --@LOOP_INVARIANT_PRESERV:FAIL @COUNTEREXAMPLE
      end loop;
   end P4;

end Counter_Example_Loop_Index;
