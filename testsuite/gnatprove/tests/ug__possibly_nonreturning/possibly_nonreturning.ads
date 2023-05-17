package Possibly_Nonreturning with
  SPARK_Mode
is

   procedure Always_Exit with
     No_Return,
     Import,
     Always_Terminates => False,
     Exceptional_Cases => (others => False);

   procedure Conditional_Exit (Cond : Boolean) with
     Always_Terminates => not Cond;

   procedure Regular with
     Always_Terminates => True;

end Possibly_Nonreturning;
