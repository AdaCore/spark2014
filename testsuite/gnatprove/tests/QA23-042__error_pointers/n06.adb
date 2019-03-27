-- Should be allowed in the final version
-- DEBUG means that the statement is here only for debug purposes and should not
-- be taken into account for the verification of lending rules.

with Ada.Text_IO;
use Ada.Text_IO;

procedure N06 is

   package Data is
      type ACI is access Integer;
      type MyStruct is record
         A,B : ACI;
      end record;

      type ACM is access MyStruct;
   end Data;
   package body Data is end Data;
   use Data;

   XA : ACI := new Integer'(10);
   XB : ACI := new Integer'(12);
   X : ACM := new MyStruct'(A => XA, B => XB);

begin
   declare
      Z : aliased ACM := X; -- move of (X) occurs here
   begin
      declare

         package DataIn is
            type ACACM is access ACM;
            function foo (X:in ACACM) return ACI;

         end DataIn;

         package body DataIn is
            function foo (X:in ACACM) return ACI --peeked (X)
            is (X.all.A); --should be legal #less precise than rust
            -- ERROR: move of (X.all.A): extension of peeked path (X)

         end DataIn;
         use DataIn;


         Y : ACACM := new ACM'(Z); --move of (Z) occurs here
         II : ACI;
      begin
         II := foo(Y); --peeking of (Y) occurs here

         -- (Y) is not peeked anymore

         XA := new Integer'(42);
         XB := new Integer'(43);
         X := new MyStruct'(A => XA, B => XB);
         --ERROR cannot assign (X): prefix of moved path (X) with 'Access

      end;
   end;
end N06;

