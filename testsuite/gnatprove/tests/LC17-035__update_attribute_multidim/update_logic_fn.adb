package body Update_Logic_Fn
  with SPARK_Mode => On
is

   procedure P1 (A  : out A2;
                 X  : in I;
                 Y  : in M;
                 V1 : in Integer;
                 V2 : in Integer)
   is
   begin
      A := A_2D_Arr'Update((5, 7) => V1, (X, Y) => V2);
   end P1;

   procedure P2 (A  : out A2;
                 X  : in I;
                 Y  : in M;
                 V1 : in Integer;
                 V2 : in Integer)
   is
   begin
      A := A_2D_Arr;
      A (5, 7) := V1;
      A (X, Y) := V2;
   end P2;

   procedure P2_False (A  : out A2;
                       X  : in I;
                       Y  : in M;
                       V1 : in Integer;
                       V2 : in Integer)
   is
   begin
      A := A_2D_Arr;
      A (5, 7) := V1;
      A (X, Y) := V2;
   end P2_False;

   procedure P3 (A  : out A3;
                 X  : in I;
                 Y  : in M;
                 Z  : in E;
                 V1 : in Integer;
                 V2 : in Integer)
   is
   begin
      A := A_3D_Arr;
      A (5, 7, Green) := V1;
      A (X, Y, Z) := V2;
   end P3;

   procedure P3_False (A  : out A3;
                       X  : in I;
                       Y  : in M;
                       Z  : in E;
                       V1 : in Integer;
                       V2 : in Integer)
   is
   begin
      A := A_3D_Arr;
      A (5, 7, Green) := V1;
      A (X, Y, Z) := V2;
   end P3_False;

   procedure P4 (A  : out A2;
                 X  : in I;
                 Y  : in M;
                 V1 : in Integer;
                 V2 : in Integer)
   is
   begin
      A := A_2D_Arr;
      A (5, 7) := V1;
      A (X, Y) := V2;
   end P4;

   procedure P5 (A  : out A2;
                 X  : in I;
                 Y  : in M;
                 V1 : in Integer;
                 V2 : in Integer)
   is
   begin
      A := A_2D_Arr;
      A (5, 7) := V1;
      A (X, Y) := V2;
   end P5;

   procedure P6 (A  : out A2;
                 X  : in I;
                 Y  : in M;
                 V1 : in Integer)
   is
   begin
      A := A_2D_Arr;
      A (5, 7) := V1;
      A (X, Y) := V1;
   end P6;

   procedure P7 (A  : out A3;
                 X1, X2  : in I;
                 Y1, Y2  : in M;
                 Z1, Z2  : in E;
                 V1 : in Integer;
                 V2 : in Integer)
   is
   begin
      A := A_3D_Arr;
      A (X1, Y1, Z1) := V1;
      A (X2, Y2, Z2) := V2;
   end P7;

   procedure P7_False (A  : out A3;
                       X1, X2  : in I;
                       Y1, Y2  : in M;
                       Z1, Z2  : in E;
                       V1 : in Integer;
                       V2 : in Integer)
   is
   begin
      A := A_3D_Arr;
      A (X1, Y1, Z1) := V1;
      A (X2, Y2, Z2) := V2;
   end P7_False;

end Update_Logic_Fn;

