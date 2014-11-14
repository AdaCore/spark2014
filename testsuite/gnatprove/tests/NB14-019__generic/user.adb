pragma SPARK_Mode;

with Gen;

procedure User is
   X : Boolean := False;
   package G is new Gen (X);
begin
   pragma Assert (not X);
end User;
