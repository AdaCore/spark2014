procedure Enum_Rep with SPARK_Mode is
   type My_Enum is (A, B, C);
   for My_Enum use (0, 12, 25);

   function My_Enum_Enumrep (X : My_Enum) return Integer
     with Post => (My_Enum_Enumrep'Result = (case X is
                       when A => 0,
                         when B => 12,
                           when C => 25));

   function My_Enum_Enumrep (X : My_Enum) return Integer
   is
   begin
      return My_Enum'Enum_Rep (X);
   end My_Enum_Enumrep;

   function My_Enum_Enumrep_2 (X : My_Enum) return Integer
     with Post => My_Enum_Enumrep_2'Result in 0 .. 2; -- incorrect

   function My_Enum_Enumrep_2 (X : My_Enum) return Integer
   is
   begin
      return My_Enum'Enum_Rep (X);
   end My_Enum_Enumrep_2;

begin
   null;
end Enum_Rep;
