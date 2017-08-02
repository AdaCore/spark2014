-- Forbidden examples : we do not want this to happen in Spark.
-- Deallocation : creating dangling pointer through aliasing.
-- DEBUG means that the statement is here only for debug purposes and should not
-- be taken into account for the verification of lending rules.

with Ada.Unchecked_Deallocation;

with Ada.Text_IO;
use Ada.Text_IO;

procedure N03 is
   package Data is
      type MyStruct is record
         A,B : aliased Integer;
      end record;
      type AM is access MyStruct;
      type AI is access all Integer;

      procedure Free_MyStruct is new Ada.Unchecked_Deallocation
        (MyStruct, AM); --Free(in out access MyStruct)
      -- move during call mode for the parameter

   end Data;
   use Data;

   X : AM := new MyStruct'(A => 10, B => 12);
   Y : AI := X.all.A'Access; --move of (X.all.A) occurs here
begin
   Put_Line ("X.all.A =" & Integer'Image(X.all.A)
             & ", X.all.B =" & Integer'Image(X.all.B)
             & ", Y.all =" & Integer'Image(Y.all)); --DEBUG

   Y.all := 14; -- assign to (Y.all): OK

   Put_Line ("X.all.A =" & Integer'Image(X.all.A)
             & ", X.all.B =" & Integer'Image(X.all.B)
             & ", Y.all =" & Integer'Image(Y.all)); --DEBUG

   Free_MyStruct(X); --explicit free, creating dangling pointer
                     --ERROR cannot move (X): prefix of moved path (X.all.A)

   Put_Line ("Y.all =" & Integer'Image(Y.all)); --/!\ use of dangling pointer

   X := new MyStruct'(A => 42, B => 43);
   -- ERROR cannot assign (X): prefix of moved path (X.all.A) under 'Access
   -- alternative rule: allowed; (X) does not have the number of .all

   Put_Line ("X.all.A =" & Integer'Image(X.all.A)
             & ", X.all.B =" & Integer'Image(X.all.B)
             & ", Y.all =" & Integer'Image(Y.all)); --DEBUG
end N03;

