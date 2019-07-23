-- Forbidden examples: we do not want this to happen in Spark.

with Ada.Text_IO;
use Ada.Text_IO;

procedure N11 is
   package Data is
      type AI is access Integer;

      subtype ACI is AI;
      procedure Modify (A : aliased in AI) with
        --no need for Depends
        Global => null;
   end Data;
   package body Data is
      procedure Modify (A : aliased in AI) is --moved (A)
         B :  ACI := A; -- move of (A.all) occurs here
         T1 : access constant AI := new AI'(A); -- move of (A) occurs here
         --ERROR: cannot move (A): prefix of moved path (A.all)
      begin
         T1.all.all := T1.all.all + 1; --assign to (T1.all.all)
      end Modify;


   end Data;
   use Data;
   X : aliased Integer := 42;
   Y : aliased AI := new Integer'(X);
begin

   Modify (Y);--move when call Y

end N11;
