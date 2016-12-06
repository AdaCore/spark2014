package Use_Var with SPARK_Mode, Initial_Condition => C = 0 is
   function Id (X : Integer) return Integer is (X);

   C : Integer := Id (0);

   D : constant Integer := C;

   type Root is tagged record
      F : Natural range D .. Integer'Last;
   end record;
end Use_Var;
