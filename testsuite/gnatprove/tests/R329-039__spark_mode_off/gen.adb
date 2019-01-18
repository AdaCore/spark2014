package body Gen with SPARK_Mode => Off is
   function Get return Integer is
   begin
      return V + 1;
   end Get;

   function Ok return Integer is
   begin
      return V + 1;
   end Ok;

   function Bad return Integer is
   begin
      return V + 1;
   end Bad;
end Gen;
