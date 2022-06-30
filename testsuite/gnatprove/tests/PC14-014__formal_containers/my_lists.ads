with SPARK.Containers.Formal.Doubly_Linked_Lists;

package My_Lists with SPARK_Mode is
   package M is new SPARK.Containers.Formal.Doubly_Linked_Lists (Positive);

   package S is new M.Generic_Sorting;

   procedure Test_List;
end My_Lists;
