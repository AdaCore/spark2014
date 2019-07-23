-- Forbidden examples: we do not want this to happen in Spark.
-- should be illegal: we claim the base pointer, creating a RW alias.

with Ada.Text_IO;
use Ada.Text_IO;

procedure N12 is
   package Data is
      type AI is access Integer;
      type AAI is access AI;

      subtype ACI is AI;
      procedure Modify (A : aliased in out AI) with
        Depends => (A => A),
        Global => null;
   end Data;
   package body Data is
      procedure Modify (A : aliased in out AI) is --move (A)
         B : ACI := A; --move of (A.all) occurs here
         T1 : AAI := new AI'(A); --move of (A) occurs here
         --ERROR: cannot move (A): prefix of moved path (A.all)
      begin
         T1.all.all := T1.all.all + 1; --assign to (T1.all.all)
      end Modify;

   end Data;
   use Data;
   X : aliased Integer := 42;
   Z : Integer := 0;
   Y : aliased AI := new Integer'(X);
begin

   Modify (Y); --move during call (Y)

end N12;
