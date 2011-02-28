package LocalCst is

   function Cst return Integer
      with Post => (Cst'Result < 10000);
   function Id (N : Integer) return Integer
      with Post => (Id'Result = N);
end LocalCst;
