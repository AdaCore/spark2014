procedure Test with SPARK_Mode is

   package Nested is
      type T (D : Integer) is private;
      pragma Predicate (T, T.D /= 0);
   private
      type T (D : Integer) is null record;
   end Nested;
begin
  null;
end Test;
