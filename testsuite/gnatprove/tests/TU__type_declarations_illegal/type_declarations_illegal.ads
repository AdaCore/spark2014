package Type_Declarations_Illegal
  with SPARK_Mode
is
   --  TU: 1. The following type declarations are not permitted in |SPARK|
   --           * ``task_type_declaration``,
   --           * ``protected_type_declaration``,
   --           * ``private_extension_declaration``,
   --           * ``interface_type_definition``, and
   --           * ``access_type_definition``.

   task type Thread (Some_Number : Integer);  --  Tasks not in SPARK

   protected type Resource is  --  Protected types not in SPARK
      entry Seize;
      procedure Release;
   private
      Busy : Boolean := False;
   end Resource;

   type Rec_T is tagged record  --  Tagged types not currently in SPARK
      A, B : Integer;
   end record;

   type Pr_Rec_T is new Rec_T with private;  --  This cannot be in SPARK
                                             --  since it requires a tagged
                                             --  type and tagged types are
                                             --  not currently in SPARK

   type Queue is Interface;  --  Interface types are not in SPARK

   type Integer_P is access Integer;  --  Access types are not in SPARK
private
   type Pr_Rec_T is new Rec_T with record
      C, D : Integer;
   end record;
end Type_Declarations_Illegal;
