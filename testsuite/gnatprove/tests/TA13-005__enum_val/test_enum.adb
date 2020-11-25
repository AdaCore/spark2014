procedure Test_Enum with SPARK_Mode is
   type My_Enum is (One, Two, Three, Four);
   for My_Enum use (0, 12, 25, 35);
   type My_Enum_2 is (One, Two, Three, Four);

   function My_Enum_Enumval (X : Integer) return My_Enum with
     Pre  => X in 0 | 12 | 25 | 35,
     Post => (My_Enum_Enumval'Result = (case X is
                  when 0  => One,
                  when 12 => Two,
                  when 25 => Three,
                  when 35 => Four,
                  when others => raise Program_Error));

   function My_Enum_Enumval (X : Integer) return My_Enum
   is
   begin
      return My_Enum'Enum_Val (X);
   end My_Enum_Enumval;

   function My_Enum_Enumval_Bad (X : Integer) return My_Enum
   is
   begin
      return My_Enum'Enum_Val (X); --@RANGE_CHECK:FAIL
   end My_Enum_Enumval_Bad;

   function Id (X : Integer) return Integer with
     Pre  => X in 0 | 12 | 25 | 35,
     Post => Id'Result = X;

   function Id (X : Integer) return Integer is
   begin
      return My_Enum'Enum_Rep (My_Enum'Enum_Val (X));
   end Id;

   function Id (X : My_Enum) return My_Enum with
     Post => Id'Result = X;

   function Id (X : My_Enum) return My_Enum is
   begin
      return My_Enum'Enum_Val (My_Enum'Enum_Rep (X));
   end Id;

   function My_Enum_Enumval (X : Integer) return My_Enum_2 with
     Pre  => X in 0 .. 3,
     Post => (My_Enum_Enumval'Result = (case X is
                  when 0  => One,
                  when 1 => Two,
                  when 2 => Three,
                  when 3 => Four,
                  when others => raise Program_Error));

   function My_Enum_Enumval (X : Integer) return My_Enum_2
   is
   begin
      return My_Enum_2'Enum_Val (X);
   end My_Enum_Enumval;

   function My_Enum_Enumval_Bad (X : Integer) return My_Enum_2
   is
   begin
      return My_Enum_2'Enum_Val (X); --@RANGE_CHECK:FAIL
   end My_Enum_Enumval_Bad;

   function Id_2 (X : Integer) return Integer with
     Pre  => X in 0 .. 3,
     Post => Id_2'Result = X;

   function Id_2 (X : Integer) return Integer is
   begin
      return My_Enum_2'Enum_Rep (My_Enum_2'Enum_Val (X));
   end Id_2;

   function Id (X : My_Enum_2) return My_Enum_2 with
     Post => Id'Result = X;

   function Id (X : My_Enum_2) return My_Enum_2 is
   begin
      return My_Enum_2'Enum_Val (My_Enum_2'Enum_Rep (X));
   end Id;
begin
   null;
end Test_Enum;
