package body Nested is

   procedure P is
      X : Integer := 0;

      procedure Incr (Z : in out Integer) with Pre => True;
      procedure Incr (Z : in out Integer) is
      begin
         Z := Z + 1;
      end Incr;
   begin
      Incr (X);
      X := X + 1;
   end P;

end Nested;
