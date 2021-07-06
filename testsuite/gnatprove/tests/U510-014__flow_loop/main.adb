procedure Main with SPARK_Mode is
   V : Integer;
begin
   for I in 1 .. 10 loop
      declare
         package Nested is
            B : Boolean := I >= 5;
            function F (X : Natural) return Integer;
            procedure P with Global => null;
         private
            B4 : Boolean;
         end Nested;
         package body Nested is
            B2 : Boolean := I <= 5;
            procedure P is null;
            function F (X : Natural) return Integer is
              (if B4 then X
               elsif B then X - 1
               elsif B2 then X - 2
               else X - 3);
         begin
            declare
               B3 : Boolean := I = 5;
            begin
               B4 := B3;
            end;
         end Nested;
      begin
         V := Nested.F (I);
      end;
   end loop;
end Main;
