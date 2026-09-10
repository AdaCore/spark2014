with Q;

--  The abstract state needs at least two constituents, so that up-projecting
--  the generated Refined_Global maps a constituent to a different item and
--  the containment check against the projected outputs is performed. Those
--  outputs also hold the magic string coming from the call to Q.Touch.

package body P with SPARK_Mode => On, Refined_State => (State => (A, B)) is

   A, B : Boolean := False;

   procedure Go is
   begin
      A := not A;
      Q.Touch;
   end Go;

end P;
