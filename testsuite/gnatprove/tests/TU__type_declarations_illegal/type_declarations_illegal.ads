package Type_Declarations_Illegal
  with SPARK_Mode
is
   --  TU: 1. The following type declarations are not permitted in |SPARK|
   --           * ``task_type_declaration``,
   --           * ``protected_type_declaration``, and
   --           * ``access_type_definition``.

   task type Thread (Some_Number : Integer);  --  Tasks not in SPARK

   protected type Resource is  --  Protected types not in SPARK
      entry Seize;
      procedure Release;
   private
      Busy : Boolean := False;
   end Resource;

   type Integer_P is access Integer;  --  Access types are not in SPARK
end Type_Declarations_Illegal;
