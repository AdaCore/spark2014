procedure Test with SPARK_Mode is
   X : constant Integer := 10;
   Y : constant Integer := 20;
   Z : Integer;
begin
   Z := X + Y;
   pragma Assert (Z = 30);
end Test;
