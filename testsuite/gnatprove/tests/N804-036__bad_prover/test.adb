procedure Test is
   X : Integer := 0;

   function Incr (Z : Integer) return Integer is (Z + 1);
begin
   X := Incr (X);
end Test;
