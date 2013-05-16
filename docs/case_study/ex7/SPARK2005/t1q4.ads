package T1Q4
is

  procedure ISQRT(N: in Natural; Root: out Natural);
  --# derives Root from N;
  --# post Root*Root <= N and
  --#      (Root+1)*(Root+1) > N;

end T1Q4;
