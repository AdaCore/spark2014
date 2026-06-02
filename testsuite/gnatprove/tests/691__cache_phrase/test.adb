procedure Test with SPARK_Mode is
   function Get return Integer
   is (0)
     with Post => True;

   X : constant Integer := Get;
   Y : constant Integer := Get;
   Z : Integer;
begin
   Z := X + Y;
end Test;
