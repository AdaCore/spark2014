-- Forbidden examples: we do not want this to happen in Spark.
-- should be legal.

with Ada.Text_IO;
use Ada.Text_IO;

procedure N15 is
   package Data is
      type AI is access Integer;

      subtype ACI is AI;
      procedure Modify (T0 : aliased in out AI) with
        Depends => (T0 => T0),
        Global => null;
   end Data;
   package body Data is
      procedure Modify (T0 : aliased in out AI) is --moved T0
         P : constant ACI := T0; --freezing *T0
                                            --move of (T0.all) occurs here

         T2 : access constant AI := new AI'(T0); -- move of (T0) occurs here
         --ERROR: cannot move (T0): prefix of moved path (T0.all)

         Q : ACI := ACI(T2.all); -- Freezing *T0 but not through P
                                 -- move of (T2.all) occurs here

         R : ACI := T0; -- Doing the same directly
                                   --move of (T0.all) occurs here
         --ERROR: cannot move (T0.all): already moved path
      begin
         null;
      end Modify;


   end Data;
   use Data;
   X : aliased Integer := 44;
   Y : aliased AI := new Integer'(X);
begin
   Modify (Y); --move of (Y) during call
end N15;
