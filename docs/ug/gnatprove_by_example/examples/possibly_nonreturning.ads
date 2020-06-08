package Possibly_Nonreturning with
  SPARK_Mode
is

   procedure Always_Exit with No_Return, Import;

   procedure Conditional_Exit (Cond : Boolean) with
     Annotate => (GNATprove, Might_Not_Return);

   procedure Regular;

end Possibly_Nonreturning;
