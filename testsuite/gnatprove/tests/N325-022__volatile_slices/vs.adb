package body VS
  with SPARK_Mode => On
is
   procedure T1 (A : out Integer)
   is
      Tmp : A4;
   begin
      Tmp := V1 (1 .. 4);
      A := Tmp (2);
   end T1;

   procedure T2 (A : out Integer)
   is
      Tmp : A4;
   begin
      Tmp := V2 (3) (1 .. 4);
      A := Tmp (2);
   end T2;

   procedure T3 (A : out Integer)
   is
      Tmp : A4;
   begin
      Tmp := V3.F2 (1 .. 4);
      A := Tmp (2);
   end T3;

   procedure T4 (A : in Integer)
   is
   begin
      V1 (1 .. 4) := A4'(A, A, A, A);
   end T4;

   procedure T5 (A : in Integer)
   is
   begin
      V2 (3) (1 .. 4) := A4'(A, A, A, A);
   end T5;

   procedure T6 (A : in Integer)
   is
   begin
      V3.F2 (2 .. 5) := (A, A, A, A);
   end T6;

end VS;
