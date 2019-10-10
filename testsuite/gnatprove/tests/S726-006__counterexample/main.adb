pragma SPARK_Mode (Off);

with finnuc; use Finnuc;
with Ada.Text_IO; use Ada.Text_IO;

procedure Main is

   Cnt : Integer := 0;
   --  count execution steps (updated in Print_Comp)

   procedure Print_Comp
     (SetA :Boolean;
      SetB: Boolean;
      C : Boolean)
   is
      A    : Boolean;
      B    : Boolean;
      OldA : Boolean;
   begin
      Cnt := Cnt + 1;

      Put_Line
        (Cnt'Img & ": SetA = " & SetA'Img
         & ", SetB = " & SetB'Img & ", C = " & C'Img);

      comp (SetA, SetB, C, A, B, OldA);

      Put_Line
        ("                                        --> A = " & A'Img
         & ", B = " & B'Img & ", OlDA = " & OldA'Img);
   end Print_Comp;

begin
   init;

   --  normally runs in loop, here we just want to show that
   --  it is used in the project
   Print_Comp(false, false, false);
   Print_Comp(false, false, false);
   Print_Comp(true, false, false);
   Print_Comp(true, false, false);
   Print_Comp(true, false, true);
   Print_Comp(true, true, true);
   Print_Comp(false, false, false);
   Print_Comp(true, false, false);
   Print_Comp(true, false, false);
   Print_Comp(true, false, false);
   Print_Comp(false, false, true);
   Print_Comp(false, false, true);
   Print_Comp(false, false, false);
   Print_Comp(false, false, false);
   Print_Comp(false, false, true);
   Print_Comp(true, false, true);
   Print_Comp(true, false, false);
   Print_Comp(false, false, false);
   Print_Comp(false, false, false);
   Print_Comp(false, false, false);
end Main;
