package body P with SPARK_Mode => Off is

   procedure Bad_Pre_Global (X : out Integer) is
   begin
      Outp := 1;
      X := 0;
   end Bad_Pre_Global;

   procedure Bad_Pre_Formal (X : out Integer) is
   begin
      X := 1;
   end Bad_Pre_Formal;

   procedure Bad_Old_Global (X : out Integer) is
   begin
      X := Outp;
      Outp := 1;
   end Bad_Old_Global;

   procedure Bad_Old_Formal (X : out Integer) is
   begin
      X := 1;
   end Bad_Old_Formal;

   procedure Ok_In_Out (X : out Integer) is
   begin
      X := Both;
   end Ok_In_Out;

   procedure Ok_Input (X : out Integer) is
   begin
      X := Inp;
   end Ok_Input;

   procedure Ok_Old (X : out Integer) is
   begin
      X := Inp + Both;
      Both := 1;
   end Ok_Old;

   procedure Missing_Global (X : out Integer) is
   begin
      X := 0;
   end Missing_Global;

   procedure Ok_Bound (X : out String) is
   begin
      X := (others => ' ');
   end Ok_Bound;

end P;
