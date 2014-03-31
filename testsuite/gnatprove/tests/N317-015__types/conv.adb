procedure Conv with
  SPARK_Mode
is
   X : Integer := 10;
   Y : Integer;

   procedure Incr (X : in Positive; Y : out Natural);

   procedure Incr (X : in Positive; Y : out Natural) is
   begin
      Y := X + 1;
   end Incr;

begin
   Incr (X, Y);
   pragma Assert (Y = 11);
end Conv;
