pragma SPARK_Mode;
procedure Arrays is
   type Arr is array (1 .. 10) of Integer;
   A : Arr;
   Y : Integer := 1;
begin
   A (1) := 0;
   A (Y) := 1;
   A (Y + 1) := 2;
   Y := Y + 5;
   A (Y) := 1;
   A (Y + 1) := 2;
end Arrays;
