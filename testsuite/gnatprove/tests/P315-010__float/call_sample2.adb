with Sample;
with Original_Sample;

procedure Call_Sample2 is

   procedure Test_Original is
      use Original_Sample;
      Nb_Of_Fp : Nb_Type := 2;
      Nb_Of_Pp : Nb_Type := 46;
      Delta_Time : Delta_Time_Type := 7.346837E-39;  --  this value is subnormal
      Time : Float := 3.6440327E-37;
   begin
      Study_Case (Nb_Of_Fp, Nb_Of_Pp, Delta_Time, Time);
   end Test_Original;

   procedure Test_New is
      use Sample;
      Nb_Of_Fp : Nb_Type := 2;
      Nb_Of_Pp : Nb_Type := 46;
      Delta_Time : Delta_Time_Type := 7.346837E-39;  --  this value is subnormal
      Time : Float := 3.6440327E-37;
   begin
      Study_Case (Nb_Of_Fp, Nb_Of_Pp, Delta_Time, Time);
   end Test_New;

begin
   Test_New;
   Test_Original;
end Call_Sample2;
