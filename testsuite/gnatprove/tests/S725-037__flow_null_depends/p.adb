package body P is
   protected body PT is
      function Id1 (X : Integer) return Integer is (Id2 (X));
      function Id2 (X : Integer) return Integer is (X);
   end PT;
end;
