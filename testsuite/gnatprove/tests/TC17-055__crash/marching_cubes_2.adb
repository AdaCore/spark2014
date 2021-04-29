package body Marching_Cubes_2
with SPARK_Mode => On
is

   procedure Q (A : access Integer; B : Integer; C: out Integer)
     with Pre => True;

   procedure Q (A : access Integer; B : Integer; C: out Integer)
   is
   begin
      if A /= null then
         A.all := 0;
      end if;
      C := B;
   end Q;

   procedure P (X : in out Holder)
     with SPARK_Mode => On
   is
      Y, Z : Integer;
      function Set_Z return Integer is (15) with Pre => True;

   begin
      Z := Set_Z;
      for I in 0 .. Z - 1 loop
	 pragma Loop_Invariant (True);
         Q (X.C, 1, Y);
      end loop;
   end P;

end Marching_Cubes_2;
