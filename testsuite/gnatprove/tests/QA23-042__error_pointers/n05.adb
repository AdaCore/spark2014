-- Forbidden examples : we do not want this to happen in Spark.
-- Creating a read access from a RW borrow : should be illegal

with Ada.Text_IO;
use Ada.Text_IO;

procedure N05 with SPARK_Mode is
   package Data is
      type ACI is access Integer;
      type MyStruct is record
         A,B : ACI;
      end record;

      type AM is access MyStruct;

   end Data;
   package body Data is end Data;
   use Data;

   XA : ACI := new Integer'(10);
   XB : ACI := new Integer'(12);
   X : AM := new MyStruct'(A => XA, B => XB);

begin
   declare
      Z : aliased AM := X; --move of (X) occurs here
   begin
      declare
         package DataIn is
            type AAM is access AM;
            function foo (X:in AAM) return ACI;

         end DataIn;

         package body DataIn is
            function foo (X:in AAM) return ACI --peeked argument (X)
            is (X.all.A); --move of (X.all.A) occurs here
            --ERROR: cannot move (X.all.A): extension of peeked path (X)

         end DataIn;
         use DataIn;

         Y : AAM := new AM'(Z); -- move of (Z) occurs here

         II : ACI;
      begin
         II := foo(Y); --peeking of (Y) occurs here

         --(Y) is not peeked anymore

         Y.all.all.A := new Integer'(12); --assign to (Y.all.all.A): OK

         XA := new Integer'(42);
         XB := new Integer'(43);
         X := new MyStruct'(A => XA, B => XB);
         --ERROR assignment (X): prefix of moved path (X) with 'Access

      end;
   end;
end N05;

