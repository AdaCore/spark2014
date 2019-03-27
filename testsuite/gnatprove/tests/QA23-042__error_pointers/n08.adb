-- Forbidden examples : we do not want this to happen in Spark.
-- should be legal : we create an RO alias from a RW pointer at the same scope
-- this would emit a restriction that will prevent the original pointer of the
-- caller to use it as W (it will hence become a RO pointer also).

with Ada.Text_IO;
use Ada.Text_IO;

procedure N08 is
   package Data is
      type AI is access Integer;
      type MyStruct is record
         A,B : AI;
      end record;
      type AM is not null access MyStruct;
      function Inc_and_get (A : in AM) return AI;
   end Data;
   package body Data is
      function Inc_and_get (A : in AM) return AI is --peeked argument (A)
      begin
         A.all.A.all := A.all.A.all + 1;
         --ERROR: cannot assign (A.all.A): extension of peeked argument (A);
         return A.all.A;
         --ERROR: cannot move (A.all.A): extension of peeked argument (A);
      end Inc_and_get;

   end Data;
   use Data;

   XA : AI := new Integer'(10);
   XB : AI := new Integer'(12);
   X : AM := new MyStruct'(A => XA, B => XB);
   Y : AM := X; --move of (X) occurs here
   Z : AI;
begin
   Z := Inc_and_get (Y); --peeking of (Y) occurs here

   --(Y) is not peeked anymore

end N08;
