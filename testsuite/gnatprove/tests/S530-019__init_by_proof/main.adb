with A;           use A;
with AA;          use AA;
with Ada.Text_IO; use Ada.Text_IO;

procedure Main
with SPARK_Mode => On,
  Global => (Output => (Global_AA, Global_AS), In_Out => File_System)
is
   X      : Natural := 0;
   status : Natural;
begin
   -- null;
   initGlobalsA(status);
   if status = 0 then
      UseA (X);
      UseAA (X);

      Ada.Text_IO.Put ("X = " & X'Image);
      Ada.Text_IO.Put ("  status = " & status'Image & ASCII.CR);
   end if;
end Main;
