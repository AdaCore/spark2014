package body Possibly_Nonterminating with
  SPARK_Mode
is
   procedure Loop_Forever is
   begin
      loop
         null;
      end loop;
   end Loop_Forever;

   procedure Conditionally_Loop (Cond : Boolean) is
   begin
      if Cond then
         Loop_Forever;
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
