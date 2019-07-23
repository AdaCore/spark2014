-- Forbidden examples: we do not want this to happen in Spark.
-- should be illegal : .

with Ada.Text_IO;
use Ada.Text_IO;

procedure N16 is
   package Data is
      type AI is access Integer;

      subtype ACI is AI;
      type ACAI is access AI;
      procedure Modify (T0 : aliased in ACAI) with
        --no need for depends
        Global => null;
   end Data;
   package body Data is
      procedure Modify (T0 : aliased ACAI) is --peeked T0
         T1 : constant ACAI := T0; -- creating alias of pointer
                                   --move of (T0) occurs here
         --ERROR: cannot move (T0): extension of peeked path (T0)

         P : AI := T0.all; -- freezing *T0
                                      --move of (T0.all.all) occurs here
         --ERROR: cannot move (T0.all.all): extension of peeked path (T0)
      begin
         T1.all.all := 42; --assign to (T1.all.all)
      end Modify;


   end Data;
   use Data;
   X : aliased Integer := 44;
   YY : aliased AI := new Integer'(X);
   Y : aliased ACAI := new AI'(YY);
begin
   Modify (Y); --peek of (Y)
end N16;
