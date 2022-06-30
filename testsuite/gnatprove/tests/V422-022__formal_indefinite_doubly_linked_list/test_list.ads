with SPARK.Containers.Formal.Indefinite_Doubly_Linked_Lists;
--  with List_pkg;

package Test_List with SPARK_Mode => On is

   package M is new SPARK.Containers.Formal.Indefinite_Doubly_Linked_Lists (Natural);
   --  package M is new List_pkg (Natural);

   package S is new M.Generic_Sorting;

   procedure Run;

   procedure Large_Run;

end Test_List;
