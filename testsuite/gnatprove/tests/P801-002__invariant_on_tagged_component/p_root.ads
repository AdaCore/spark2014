package P_Root with SPARK_Mode is
   type Root is tagged null record;

   function F (X : Root) return Natural is (0);
end P_Root;
