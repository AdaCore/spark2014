procedure Preserved_Components with SPARK_Mode is

   type A is array (1 .. 100) of Natural with Default_Component_Value => 1;

   type A_Matrix is array (1 .. 100, 1 .. 100) of A;

   M : A_Matrix;

begin
   L1: for I in 1 .. 100 loop
      M (I, 1) (1 .. 50) := (others => 0);
      pragma Assert
        (for all K1 in 1 .. 100 =>
           (for all K2 in 1 .. 100 =>
                (for all K3 in 1 .. 100 =>
                     (if K1 > I or else K2 /= 1 or else K3 > 50 then
                             M (K1, K2) (K3) = M'Loop_Entry (K1, K2) (K3)))));
   end loop L1;

   L2: for I in 1 .. 99 loop
      M (I + 1, I) (I .. 100) := (others => 0);
      pragma Assert
        (for all K1 in 1 .. 100 =>
           (for all K2 in 1 .. 100 =>
                (for all K3 in 1 .. 100 =>
                     (if K1 > I + 1 then
                             M (K1, K2) (K3) = M'Loop_Entry (K1, K2) (K3)))));
      pragma Assert
        (for all K1 in 1 .. 100 =>
           (for all K2 in 1 .. 100 =>
                (for all K3 in 1 .. 100 =>
                     (if K3 < K2 then
                             M (K1, K2) (K3) = M'Loop_Entry (K1, K2) (K3)))));
   end loop L2;

end Preserved_Components;
