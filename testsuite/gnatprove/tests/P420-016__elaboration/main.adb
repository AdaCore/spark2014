with Globs;

procedure Main
  with SPARK_Mode
is
begin
   pragma Assert (Globs.X);
   pragma Assert (Globs.Y);
end Main;
