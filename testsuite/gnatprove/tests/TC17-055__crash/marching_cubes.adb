package body Marching_Cubes
with SPARK_Mode => On
is

   procedure Q (A : access Integer; B : Integer; C: out Integer);

   procedure Q (A : access Integer; B : Integer; C: out Integer)
     with SPARK_Mode => Off
   is
   begin
      C := B;
   end Q;

   procedure P (X : not null access Integer)
     with SPARK_Mode => On
   is
      Y, Z : Integer;
      function Set_Z return Integer is (0) with Pre => True;

   begin
      Z := Set_Z;
      for I in 0 .. Z - 1 loop
         Q (X, 1, Y);
      end loop;
   end P;

end Marching_Cubes;
