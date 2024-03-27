package body Gen with SPARK_Mode is

   procedure PP (X : in out T) is
   begin
      X := 0;
   end PP;

   package body Nested is
      procedure PPP (X : in out T) is
      begin
         X := 0;
      end PPP;
   end Nested;

end Gen;
