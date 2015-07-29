procedure G is
   generic
      type Index_T is (<>);
   package G_Pkg is
      function Foo return Integer;
   end G_Pkg;

   package body G_Pkg is
      Tmp : Integer;

      function Foo return Integer is (Tmp);
   begin
      Tmp := 10;
   end G_Pkg;

   type My_Range is range -10 .. 10;

   package Inst is new G_Pkg (Index_T => My_Range);

begin
   pragma Assert (Inst.Foo = 10);
end G;
