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

   -- 2D array update
   procedure P3 (A2D : in out Arr_2D) is
   begin
       A2D (1, 1) := 1;
       A2D (2, 2) := 2;
       A2D (3, 3) := 3;
   end P3;

   -- Nested record update
   procedure P4 (NR : in out Nested_Rec) is
   begin
       NR.A     := 1;
       NR.B.X   := 1;
       NR.C (1) := 5;
   end P4;

   -- Nested array update
   procedure P5 (NA : in out Nested_Arr) is
   begin
       NA (1).A        := 1;
       NA (1).D (2, 2) := 0;
       NA (2).B.X      := 2;
       NA (3).C (1)    := 5;
   end P5;

end Update_Examples;
