with Gen_Pack;

procedure Main is

   type My_Int is range -100 .. 100;

   type Other_Int is range 0 .. 10000;

   package Inst1 is new Gen_Pack (My_Int);
   package Inst2 is new Gen_Pack (Other_Int);
begin
   null;
end Main;
