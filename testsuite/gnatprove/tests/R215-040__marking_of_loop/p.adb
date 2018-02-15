package body P with SPARK_Mode is

   procedure Dummy (L : My_Lists.List) is
   begin
      for J : Not_In_SPARK.Bad_Int of L loop
      --      ^^^^^^^^^^^^^^^^^^^^ this type is not in SPARK
         pragma Assert (J >= 0);
      end loop;
   end Dummy;

end P;
