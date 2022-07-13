with Ada.Text_IO; use Ada.Text_IO;

procedure Main with SPARK_Mode is
   package Nested is
      type R1 is record
         A : Integer;
         B : Integer;
      end record;
      function "=" (X, Y : R1) return Boolean is (X.A = Y.A);
   end Nested;
   use Nested;

   type R2 is new R1;
   function "=" (X, Y : R2) return Boolean is (X.B = Y.B);

   type RR1 is record
      F : R1;
   end record;
   type RR2 is record
      F : R2;
   end record;

   X : RR1 := (F => (1, 1));
   Y : RR1 := (F => (1, 2));

   Z : RR2 := (F => (1, 1));
   W : RR2 := (F => (1, 2));
begin
   Put_Line ("A");

   if X = Y then
   Put_Line ("B");
   end if;

   if Z = W then
   Put_Line ("C");
   end if;
end;
