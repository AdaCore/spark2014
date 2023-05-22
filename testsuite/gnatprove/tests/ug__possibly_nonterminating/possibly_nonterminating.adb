package body Possibly_Nonterminating with
  SPARK_Mode
is
   procedure Loop_Forver is
   begin
      loop
         null;
      end loop;
   end Loop_Forver;

   procedure Conditionally_Loop (Cond : Boolean) is
   begin
      if Cond then
         Loop_Forver;
      end if;
   end Conditionally_Loop;

   procedure Ok_Terminating is
   begin
      Conditionally_Loop (False);
   end Ok_Terminating;

   procedure Bad_Terminating is
   begin
      Conditionally_Loop (True);
   end Bad_Terminating;

end Possibly_Nonterminating;
