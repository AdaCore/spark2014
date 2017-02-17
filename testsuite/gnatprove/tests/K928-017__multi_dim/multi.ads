package Multi is

   type A2 is array (1 .. 2) of Integer;
   type A4 is array (1 .. 2, 1 .. 2) of Integer;

   One : Integer;

   procedure P4 (A : in out A4; B : Integer) with
     Pre => One = 1,
     Post => (case B is when 1 => (for all K in A4'Range => A (K, One) = One and A (K, 2) = 2),
                        when 2 => (for all J in A2'Range => (for all K in A2'Range(1) => A (J, K) = One)),
                        when 3 => (for all J in A2'Range => (for all K in A2'Range(1) => A (J, K) = One)),
                        when 4 => (for all J in A2'Range => (for all K in A2'Range(1) => A (J, K) = (if J = 1 and K = 1 then 2 else One))),
                        when others => (for all J in A2'Range => (for all K in A2'Range(1) => A (J, K) = (if J = 2 and K = 1 then 2 else One))));

end Multi;
