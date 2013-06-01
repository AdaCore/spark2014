package LocalCst is

   function Cst return Integer
      with Post => (Cst'Result < 10000);

   function Id (N : Integer) return Integer
      with Post => (Id'Result = N);

   function Glob return Integer
      with Post => (Glob'Result < 4000);

end LocalCst;
