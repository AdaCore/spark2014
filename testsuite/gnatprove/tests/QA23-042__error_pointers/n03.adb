-- Forbidden examples : we do not want this to happen in Spark.
-- Deallocation : creating dangling pointer through aliasing.

with Ada.Unchecked_Deallocation;

with Ada.Text_IO;
use Ada.Text_IO;

procedure N03 is
   package Data is
      type AI is access Integer;
      type MyStruct is record
         A,B : AI;
      end record;
      type AM is access MyStruct;

      procedure Free_MyStruct is new Ada.Unchecked_Deallocation
        (MyStruct, AM); --Free(in out access MyStruct)
      -- move during call mode for the parameter

   end Data;
   use Data;

   XA : AI := new Integer'(10);
   XB : AI := new Integer'(12);
   X : AM := new MyStruct'(A => XA, B => XB);
   Y : AI := X.all.A; --move of (X.all.A) occurs here
begin
   Y.all := 14; -- assign to (Y.all): OK

   Free_MyStruct(X); --explicit free, creating dangling pointer
                     --ERROR cannot move (X): prefix of moved path (X.all.A)

   Put_Line ("Y.all =" & Integer'Image(Y.all)); --/!\ use of dangling pointer


   XA := new Integer'(42);
   XB := new Integer'(43);
   X := new MyStruct'(A => XA, B => XB);
   -- ERROR cannot assign (X): prefix of moved path (X.all.A) under 'Access
   -- alternative rule: allowed; (X) does not have the number of .all

end N03;

