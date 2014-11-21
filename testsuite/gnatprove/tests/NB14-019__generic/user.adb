pragma SPARK_Mode;

with Gen;

procedure User is
   X : Boolean := True;
   package G is new Gen (X);
begin
   X := G.Y;
   pragma Assert (not X);
end User;
