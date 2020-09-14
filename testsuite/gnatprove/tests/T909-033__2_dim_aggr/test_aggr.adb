procedure Test_Aggr with SPARK_Mode is
   type Matrice is array (Positive range <>, Positive range <>) of Integer;
   A : Matrice := (for I in 1 .. 10 => (I, I + 1, I - 1, 0));
begin
   pragma Assert (for all I in A'Range (1) => A (I, 1) = I);
   pragma Assert (for all I in A'Range (1) => A (I, 4) = 0);
end Test_Aggr;
