-- Forbidden examples : we do not want this to happen in Spark.
-- Aliased Read-Write access.

with Ada.Text_IO;
use Ada.Text_IO;

procedure N01 with SPARK_Mode is
   package Data is
      type AI is access Integer;
      type MyStruct is record
         A,B : AI;
      end record;
   end Data;
   use Data;

   X : MyStruct;

begin
   X.A := new Integer'(10);
   X.B := new Integer'(12);

   declare
      Y : constant AI := X.A; -- move of (X.A) occurs here.
   begin
      Y.all := 12; --Assign to (Y.all): OK

      X.A.all := 42;
      X.B.all := 43;
      -- ERROR, assignment to (X): prefix of moved path (X.A) with 'Access
   end;
end N01;
