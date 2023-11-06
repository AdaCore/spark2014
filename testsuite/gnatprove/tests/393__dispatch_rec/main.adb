procedure Main with SPARK_Mode is

   package Nested is
      type Root is tagged record
         F : Integer;
      end record;
      function G (X : Root; K : Integer) return Integer with Post'Class => False;
   end Nested;

   package body Nested is
      function G (X : Root; K : Integer) return Integer is
         V : Root'Class := Root'(F => 0);
         I : Integer := (if X.F > 0 then G (V, K) else 0);
         J : Integer := (if K > 0 then G (X, 0) else 0);
      begin
         return I + J;
      end G;
   end Nested;

begin
   null;
end Main;
