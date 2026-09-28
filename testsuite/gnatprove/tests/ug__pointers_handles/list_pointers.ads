pragma Extensions_Allowed (On);

with SPARK.Pointers.Auto_Reclaimed.Immutable;
with SPARK.Pointers.Handles.Auto_Reclaimed_Handles;

package List_Pointers with SPARK_Mode is

   package Cell_Handles is new
     SPARK.Pointers.Handles.Auto_Reclaimed_Handles.Without_Weak_Handles;

   type Cell is record
      Value : Integer;
      Next  : aliased Cell_Handles.Handle;
   end record;

   package Lists is new SPARK.Pointers.Auto_Reclaimed.Immutable (Cell);
   package Ops is new Lists.Handle_Operations (Cell_Handles);

   function Next_Of
     (C : not null access constant Cell)
      return access constant Cell_Handles.Handle
   is (C.Next'Access)
   with Global => null;

   package Variant is new Ops.Structural_Variant (Next_Of);

   function Id (C : Cell) return Cell is (C);
   function Create_Cell is new Lists.Create (Cell, Id);

end List_Pointers;
