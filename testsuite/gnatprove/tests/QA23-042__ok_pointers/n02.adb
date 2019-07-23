-- Creating a memory leak.

with Ada.Text_IO;
use Ada.Text_IO;

procedure N02 with SPARK_Mode is
   package Data is
      type AI is not null access Integer;
      type MyStruct is record
         A,B : AI;
      end record;
      type AM is not null access MyStruct;
   end Data;
   use Data;

   XA : AI := new Integer'(10);
   XB : AI := new Integer'(12);
   X : AM := new MyStruct'(A => XA, B => XB);
   Y : constant AI := X.all.A; --move of (X.all.A) occurs here
begin
   Y.all := 14; -- assign to (Y.all): OK

   XA := new Integer'(42);
   XB := new Integer'(43);
   X := new MyStruct'(A => XA, B => XB);
   --if deallocation of old X there then dangling pointer Y created

   Put_Line ("X.all.A =" & Integer'Image(X.all.A.all)
             & ", X.all.B =" & Integer'Image(X.all.B.all)
             & ", Y.all =" & Integer'Image(Y.all));
end N02;
