-- This example is to show that the analysis is field sensitive. If X is a struct with X.A being aliased
-- then, this is not necessarly the case for X.B.

with Ada.Text_IO;
use Ada.Text_IO;

procedure N011 with SPARK_Mode is
   package Data is
      type MyStruct is record
         A,B : aliased Integer;
      end record;
      type AI is access all Integer;
   end Data;
   use Data;

   var : integer;
   var2 : integer;
   X : MyStruct := (A => 10, B => 12);
   Y : constant AI := X.A'Access; -- move of (X.A) occurs here.
begin
   var := X.A; --  ERROR reported: insufficient permission for "X" expected at least "read_only", got "no_access"
   var2 := X.B;
   Y.all := 12; --Assign to (Y.all): OK
end N011;
