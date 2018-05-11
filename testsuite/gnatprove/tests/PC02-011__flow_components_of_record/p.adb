package body P is
   protected body PT is
      function F return Integer is (X.all);
   end PT;

   protected body PO2 is
      function Fun2 return Integer is (X);
   end PO2;
end P;
