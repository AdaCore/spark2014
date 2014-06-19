with Gen;
procedure User with
  SPARK_Mode
is
   X : Integer;
   Y : Integer;
   package Gen_X is new Gen (X);
   package Gen_Y is new Gen (Y);
begin
   Gen_X.Set (0);
   pragma Assert (Gen_X.Get = 0);
   Gen_Y.Set (1);
   pragma Assert (Gen_Y.Get = 0);
end User;
