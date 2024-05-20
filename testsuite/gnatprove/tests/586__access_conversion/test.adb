procedure Test with SPARK_Mode is

   package Nested is
      type P is private;
   private
      type P is access constant Integer with Type_Invariant => True;

      type T is access constant Integer;

      function F (X : P) return T is (T (X));
   end Nested;
begin
  null;
end Test;
