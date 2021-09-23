with Q1;
package body R1 with Refined_State => (R1_State => R2.R2_State)
is
   package body R2
     with Refined_State => (R2_State => (TA, B))
   is
      B : Boolean := True;
      TA : T1;
      task body T1 is
      begin
         Q1.Flip;
         B := not B;
      end T1;
   end;

end R1;
