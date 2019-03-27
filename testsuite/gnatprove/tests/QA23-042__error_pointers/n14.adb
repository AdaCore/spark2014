-- Forbidden examples: we do not want this to happen in Spark.
-- should be illegal : freezing the base pointer with a different path.

with Ada.Text_IO;
use Ada.Text_IO;

procedure N14 is
   package Data is
      type AI is access Integer;
      type AAI is access AI;

      procedure Modify (T0 : aliased in out AI) with
        Depends => (T0 => T0),
        Global => null;
   end Data;
   package body Data is
      procedure Modify (T0 : aliased in out AI) is --moved T0
         P : constant AI := T0; --claiming reference
                                           --move of (T0.all) occurs here

         T2 : access constant AI := new AI'(T0); --move of (T0) occurs here
         --ERROR: cannot move (T0): prefix of moved path (T0.all)

         Q : access constant AI := T2; -- Freezing T0 but not through P
                                                  --moving (T2.all) : ok
      begin
         P.all := P.all + 1; -- Violates type of *Q;
                             -- nothing moved there, assign (P.all)
      end Modify;


   end Data;
   use Data;
   X : aliased Integer := 44;
   Y : aliased AI := new Integer'(X);
begin
   Modify (Y);
end N14;
