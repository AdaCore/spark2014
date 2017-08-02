-- Forbidden examples : we do not want this to happen in Spark.
-- Aliased Read-Write access.
-- DEBUG means that the statement is here only for debug purposes and should not
-- be taken into account for the verification of lending rules.

with Ada.Text_IO;
use Ada.Text_IO;

procedure N01 with SPARK_Mode is
   package Data is
      type MyStruct is record
         A,B : aliased Integer;
      end record;
      type AI is access all Integer;
   end Data;
   use Data;

   X : MyStruct := (A => 10, B => 12);
   Y : constant AI := X.A'Access; -- move of (X.A) occurs here.
begin
   Put_Line ("X.A =" & Integer'Image(X.A) 
             & ", X.B =" & Integer'Image(X.B) 
             & ", Y.all =" & Integer'Image(Y.all)); --DEBUG
   Y.all := 12; --Assign to (Y.all): OK
   
   Put_Line ("X.A =" & Integer'Image(X.A) 
             & ", X.B =" & Integer'Image(X.B) 
             & ", Y.all =" & Integer'Image(Y.all)); --DEBUG
   
   X := (A => 42, B => 43); 
   -- ERROR, assignment to (X): prefix of moved path (X.A) with 'Access
   
   Put_Line ("X.A =" & Integer'Image(X.A) 
             & ", X.B =" & Integer'Image(X.B) 
             & ", Y.all =" & Integer'Image(Y.all)); --DEBUG
end N01;
