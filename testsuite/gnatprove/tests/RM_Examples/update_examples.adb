package body Update_Examples
  with SPARK_Mode
is
   -- Simple record update
   procedure P1 (R : in out Rec) is
   begin
      R.X := 1;
   end P1;

   -- Simple 1D array update
   procedure P2 (A : in out Arr) is
   begin
      A (1) := 2;
   end P2;

   -- Nested record update
   procedure P3 (NR : in out Nested_Rec) is
   begin
       NR.A     := 1;
       NR.B.X   := 1;
       NR.C (1) := 5;
   end P3;

   -- Nested array update
   procedure P4 (NA : in out Nested_Arr) is
   begin
       NA (1).A        := 1;
       NA (2).B.X      := 2;
       NA (3).C (1)    := 5;
   end P4;

end Update_Examples;
