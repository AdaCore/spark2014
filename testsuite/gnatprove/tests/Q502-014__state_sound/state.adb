pragma SPARK_Mode;

package body State with
  Refined_State => (State => (S1, S2))
is

   S2 : Integer := 0;

   procedure Set (X : Integer)
   is
   begin
      S2 := X;
   end Set;

   function Get return Integer is (S2);

end State;
