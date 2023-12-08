package Ext with SPARK_Mode is

   --  Annotations are correct and should not be rejected even on user packages

   function Id (X : Integer) return Integer with
     Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");

   function Id_2 (X : Integer) return Integer is
     (Id (X))
   with Post => Id_2'Result = X;
   pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Id);

end Ext;
