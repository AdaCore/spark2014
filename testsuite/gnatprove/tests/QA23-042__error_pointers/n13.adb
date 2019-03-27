-- Forbidden examples: we do not want this to happen in Spark.
-- should be illegal : we create a new path by swapping the two adresses.

with Ada.Text_IO;
use Ada.Text_IO;

procedure N13 is
   package Data is
      type AI is access Integer;
      type AAI is access AI;

      subtype ACI is AI;
      procedure Modify (A : in out AI ; BB : in out AI) with
        Depends => (A => (BB), BB => (A)),
        Global => null;
   end Data;
   package body Data is
      procedure Modify (A : in out AI ; BB : in out AI) is --move (A) move (BB)
         B : ACI := A; --freezing reference
                                  --move of (A.all occurs here)

         --Note that without the first line, this code would compile and work
         -- without any problem (it would be a simple swap and assign).

         T : AI := A; --move of (A) occurs here
         --ERROR: cannot move (A): prefix of moved path (A.all)
      begin
         A := BB; --move of BB occurs here
                  --assign to A, restriction lifted here
         BB := T; --move of T occurs here,
                  --assign to BB, restriction lifted here

         A.all := 42; --assign to (A.all) -> ok
      end Modify;

   end Data;
   use Data;
   X : aliased Integer := 44;
   XX : aliased Integer := 55;
   Y : aliased AI := new Integer'(X);
   YY : aliased AI := new Integer'(XX);
begin

   Modify (Y, YY); -- move (Y) and (YY)

end N13;
