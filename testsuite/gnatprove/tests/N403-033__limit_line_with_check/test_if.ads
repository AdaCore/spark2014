package Test_If is

   function  Test (A : integer) return Integer with
     Pre => (A = 0 or else A = 1),
     Post => (Test'Result = A * 500 + 500 + 3);

end Test_If;
