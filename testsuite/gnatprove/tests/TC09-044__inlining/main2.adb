procedure Main2 with SPARK_Mode is

   function Incr (X : Integer) return Integer is
   begin
      return X + 1;
   end Incr;

   B : constant Boolean := Incr (Integer'Last) > Integer'Last;
begin
   pragma Assert (B);
end Main2;
