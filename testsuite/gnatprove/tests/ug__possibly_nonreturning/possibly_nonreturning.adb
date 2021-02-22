package body Possibly_Nonreturning with
  SPARK_Mode
is

   procedure Conditional_Exit (Cond : Boolean) is
   begin
      if Cond then
         Always_Exit;
      end if;
   end Conditional_Exit;

   procedure Regular is
   begin
      Conditional_Exit (True);
   end Regular;

end Possibly_Nonreturning;
