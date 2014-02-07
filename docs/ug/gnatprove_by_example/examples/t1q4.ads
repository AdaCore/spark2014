package T1Q4
  with SPARK_Mode
is

   procedure ISQRT (N : in Natural; Root : out Natural)
     with Post => (Root * Root <= N and
                   (Root + 1) * (Root + 1) > N);

end T1Q4;
