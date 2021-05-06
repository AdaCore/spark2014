--  A hierarchy of packages (R1/2/3) with synchronized and unsychronized
--  states (S1/2/3 and U1/2/3, respectively)
--  Desired result is to identify that R3.U3 is subject to possible race
--  from the two tasks declared in the package body.
package R1 with SPARK_Mode,
  Abstract_State => (S1,U1),
  Initializes => (S1, U1)
is
private
   package R2 with
     Abstract_State => ((S2 with Part_Of => S1), (U2 with Part_Of => U1)),
     Initializes => (S2, U2)
   is
      task type TT2 with Global => (In_Out => U2);

      private

         package R3 with
           Abstract_State => ((S3 with Part_Of => S2), (U3 with Part_Of => U2)),
           Initializes => (S3, U3)
         is
            procedure Flip with Global => (In_Out => U3);
         end R3;
   end R2;
end R1;
