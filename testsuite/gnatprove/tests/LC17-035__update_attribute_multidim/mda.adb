package body MDA
  with SPARK_Mode => On
is
   procedure Set2C (A : in out A2;
                    X : in I;
                    Y : in M;
                    V : in Integer)
   is
   begin
      A (X, Y) := V;
   end Set2C;

   procedure Set2U (A : in out A2U;
                    X : in I;
                    Y : in M;
                    V : in Integer)
   is
   begin
      A (X, Y) := V;
   end Set2U;

   procedure Set3C (A : in out A3;
                    X : in I;
                    Y : in M;
                    Z : in E;
                    V : in Integer)
   is
   begin
      A (X, Y, Z) := V;
   end Set3C;

   procedure Set3U (A : in out A3U;
                    X : in I;
                    Y : in M;
                    Z : in E;
                    V : in Integer)
   is
   begin
      A (X, Y, Z) := V;
   end Set3U;

   procedure Set2E2C (A  : in out A2;
                      X1 : in I;
                      Y1 : in M;
                      X2 : in I;
                      Y2 : in M;
                      V1 : in Integer;
                      V2 : in Integer)
   is
   begin
      A (X1, Y1) := V1;
      A (X2, Y2) := V2;
   end Set2E2C;

   procedure Set2E2U (A  : in out A2U;
                      X1 : in I;
                      Y1 : in M;
                      X2 : in I;
                      Y2 : in M;
                      V1 : in Integer;
                      V2 : in Integer)
   is
   begin
      A (X1, Y1) := V1;
      A (X2, Y2) := V2;
   end Set2E2U;

   procedure Set2E3C (A  : in out A3;
                      X1 : in I;
                      Y1 : in M;
                      Z1 : in E;
                      X2 : in I;
                      Y2 : in M;
                      Z2 : in E;
                      V1 : in Integer;
                      V2 : in Integer)
   is
   begin
      A (X1, Y1, Z1) := V1;
      A (X2, Y2, Z2) := V2;
   end Set2E3C;

   procedure Set2E3U (A  : in out A3U;
                      X1 : in I;
                      Y1 : in M;
                      Z1 : in E;
                      X2 : in I;
                      Y2 : in M;
                      Z2 : in E;
                      V1 : in Integer;
                      V2 : in Integer)
   is
   begin
      A (X1, Y1, Z1) := V1;
      A (X2, Y2, Z2) := V2;
   end Set2E3U;

end MDA;
