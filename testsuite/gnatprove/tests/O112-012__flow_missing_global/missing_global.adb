package body Missing_Global is
   procedure P1 (X : out Integer) is
   begin
      P2 (X);
   end P1;

   procedure P2 (X : out Integer)
     with SPARK_Mode => Off
   is
   begin
      P3 (X);
   end P2;

   procedure P3 (X : out Integer)
     with SPARK_Mode => Off
   is
   begin
      X := G1 + G2;
   end P3;
end Missing_Global;
