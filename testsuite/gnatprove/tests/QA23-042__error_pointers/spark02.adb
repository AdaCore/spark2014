-- Should be allowed, if we allow pointers in functions (and not only
-- in procedures)

with Ada.Text_IO;
use Ada.Text_IO;

procedure Spark02 is
   package Data is
      type AI is access Integer;
      function Foo (x : AI) return AI;

      function Bar (x:Integer) return Integer is (x);
      procedure Test (x : in out Integer);
   end Data;
   package body Data is
      function Foo (x:AI) return AI is --peeked (x)
      begin
         return x; --move of (X) occurs here
         --ERROR, cannot move (X): peeked path (X)
      end Foo;
      procedure Test (x : in out Integer) is
      begin
         x := 42;
      end Test;
   end Data;
   use Data;
   X : aliased Integer := 44;
   Y : aliased AI := new Integer'(X);
   Z : aliased AI := new Integer'(X);
begin
   Put_Line ("X = " & Integer'Image(X) );
   Foo(Y).all := 5; --peek of (Y) occurs here

   Test(Foo(Y).all);
   Test(AI'(if True then Y else Y).all);
   Put_Line ("X = " & Integer'Image(X) );
end Spark02;


