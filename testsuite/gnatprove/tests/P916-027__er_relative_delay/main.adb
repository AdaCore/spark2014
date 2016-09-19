procedure Main is
   function Zero return Integer is (0);
   One : Standard.Duration := 1.0;
begin
   delay One / Zero;
   delay -1.0;
   delay 0.0;
   delay 1.0;
end;
