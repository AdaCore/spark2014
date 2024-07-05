package Possibly_Nonterminating with
  SPARK_Mode
is

   procedure Loop_Forever with
     No_Return,
     Always_Terminates => False,
     Exceptional_Cases => (others => False);

   procedure Conditionally_Loop (Cond : Boolean) with
     Always_Terminates => not Cond;

   procedure OK_Terminating with
     Always_Terminates;

   procedure Bad_Terminating with
     Always_Terminates;

end Possibly_Nonterminating;
