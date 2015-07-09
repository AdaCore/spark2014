package Cst
  with SPARK_Mode
is
   type T is array (1 .. 10) of Integer;
   X : T := (others => 1);
   J : Integer := 3;
   Y : constant Integer := X(3);

   function Get_Y return Integer is (Y);
end Cst;
