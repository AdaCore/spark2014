-- Forbidden examples : we do not want this to happen in Spark.
-- Already forbidden by Ada. scope escape

with Ada.Text_IO;
use Ada.Text_IO;

procedure N04 is
   package Data is
      type AI is access Integer;
      type MyStruct is record
         A,B : access Integer;
      end record;

      type AM is access MyStruct;
      function foo (X:access MyStruct) return access Integer;
      Y : access Integer;

   end Data;

   package body Data is
      function foo (X:access MyStruct) return access Integer
      is (X.all.A);

   end Data;
   use Data;


begin
   declare --LT1
      XA : AI := new Integer'(10);
      XB : AI := new Integer'(12);
      XX : AM := new MyStruct'(A => XA, B => XB);
      X : access MyStruct := XX;
      -- creating local object with lifetime LT1
   begin

      Y := foo(X);
      -- ERROR non-local pointer cannot point to local object

      end;
end N04;

