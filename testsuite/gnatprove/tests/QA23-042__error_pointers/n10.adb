-- Forbidden examples: we do not want this to happen in Spark.
-- should be illegal: we move a freezed reference, creating an alias.
-- DEBUG means that the statement is here only for debug purposes and should not
-- be taken into account for the verification of lending rules.

with Ada.Text_IO;
use Ada.Text_IO;

procedure N10 is
   package Data is
      type AI is access Integer;
      procedure Modify (A : in AI) with
        -- No need for Depends
        Global => null;

   end Data;
   package body Data is
      procedure Modify (A : in AI) is --moved (A)
         B : AI := A; --move of (A.all) occurs here
         T1 : AI := A; --move of (A) occurs here
         --ERROR: cannot move (A): prefix of moved path (A.all)
      begin
         T1.all := 42;
      end Modify;


   end Data;
   use Data;
   X : aliased Integer := 1;
   Y : AI := new Integer'(X); --move of (X) occurs here
begin

   Modify(Y); --move when call Y

end N10;
