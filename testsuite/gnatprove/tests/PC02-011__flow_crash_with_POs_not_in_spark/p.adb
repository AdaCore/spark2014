package body P
is
   protected body PT is
      function Fun return Integer is (X);
   end PT;

   protected body PO2 is
      function Fun2 return Integer is (X);
   end PO2;
end P;
