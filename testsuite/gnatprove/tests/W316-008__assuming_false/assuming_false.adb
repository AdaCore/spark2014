procedure Assuming_False with SPARK_Mode is
   X : Integer := 0;
   Y : Integer := 1;
begin
   pragma Assume (False);
   pragma Assert (X = Y);
end Assuming_False;
