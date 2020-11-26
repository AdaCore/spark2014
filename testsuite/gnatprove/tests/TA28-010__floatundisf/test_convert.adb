with Convert;
with Interfaces; use Interfaces;
with Ada.Text_IO; use Ada.Text_IO;

procedure Test_Convert is
   R   : Convert.Binary32;
   Bad : Unsigned_64 := 2**47 + 2**24;
begin
   for V in Unsigned_64 range 0 .. Bad - 1 loop
      R := Convert.Floatundisf (V);
   end loop;
   Put_Line ("Testing bad value " & Bad'Img);
   R := Convert.Floatundisf (Bad);
end Test_Convert;
