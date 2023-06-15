with SPARK.Containers.Functional.Sets;

package Formal_Cont with
  SPARK_Mode
is
   -- NONRETURNING CASE

   -- Nonreturning instantiation of "="
   function My_Equal_01 (A, B : Integer) return Boolean;

   -- Package instantiation with nonreturning subprogram
   package New_Set_01 is new SPARK.Containers.Functional.Sets
     (Element_Type       => Integer,
      Equivalent_Elements => My_Equal_01);
   use New_Set_01;

   -- Test procedure for nonreturning instantiation
   procedure Test_01 with Always_Terminates;

   -- RETURNING CASE

   -- Returning instantiation of "="
   function My_Equal_02 (A, B : Integer) return Boolean;

   -- Package instantiation with returning subprogram
   package New_Set_02 is new SPARK.Containers.Functional.Sets
     (Element_Type        => Integer,
      Equivalent_Elements => My_Equal_02);
   use New_Set_02;

   -- Test procedure for returning instantiation
   procedure Test_02 with Always_Terminates;

end Formal_Cont;
