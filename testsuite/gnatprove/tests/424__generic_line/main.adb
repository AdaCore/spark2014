with Gen;
with Gen2;
procedure Main is
  package I1 is new Gen (Integer);
  X : Integer := 0;
  package I2 is new Gen (Natural);
  Y : Natural := Natural'Last;

  type T is range 0 .. 255;
  Z : T := 254;
  package I3 is new Gen (T);

  package I4 is new Gen2 (T);
begin
  I1.Incr (X);
  I2.Incr (Y);
  I3.Incr (Z);
  I4.My_Incr (Z);
end Main;
