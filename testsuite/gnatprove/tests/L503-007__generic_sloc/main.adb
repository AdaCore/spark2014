with Gen;

procedure Main is pragma SPARK_Mode (On);
   type Sub is new Integer range 1 .. 10;
   package A is new Gen (Integer);
   package B is new Gen (Sub);
   X : Integer := 0;
   Y : Sub := 1;
begin
   A.R (X);
   B.R (Y);
end Main;
