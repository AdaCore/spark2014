-- Creating a memory leak.
-- DEBUG means that the statement is here only for debug purposes and should not
-- be taken into account for the verification of lending rules.

with Ada.Text_IO;
use Ada.Text_IO;

procedure N02 with SPARK_Mode is
   package Data is
      type MyStruct is record
         A,B : aliased Integer;
      end record;
      type AM is not null access all MyStruct;
      type AI is not null access all Integer;
   end Data;
   use Data;

   X : AM := new MyStruct'(A => 10, B => 12);
   Y : constant AI := X.all.A'Access; --move of (X.all.A) occurs here
begin
   Put_Line ("X.all.A =" & Integer'Image(X.all.A)
             & ", X.all.B =" & Integer'Image(X.all.B)
             & ", Y.all =" & Integer'Image(Y.all)); --DEBUG

   Y.all := 14; -- assign to (Y.all): OK

   Put_Line ("X.all.A =" & Integer'Image(X.all.A)
             & ", X.all.B =" & Integer'Image(X.all.B)
             & ", Y.all =" & Integer'Image(Y.all)); --DEBUG

   X := new MyStruct'(A => 42, B => 43);
   --if deallocation of old X there then dangling pointer Y created
   --ERROR cannot assign to (X): prefix of moved path (X.all.A) under 'Access
   --alternative rule: allowed; (X) does not have the same number of .all

   Put_Line ("X.all.A =" & Integer'Image(X.all.A)
             & ", X.all.B =" & Integer'Image(X.all.B)
             & ", Y.all =" & Integer'Image(Y.all)); --DEBUG
end N02;
