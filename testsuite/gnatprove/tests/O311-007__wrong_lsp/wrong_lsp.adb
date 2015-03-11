package body Wrong_LSP with SPARK_Mode is

   procedure Do_Nothing (R : in out Root) is
   begin
      null;
   end Do_Nothing;

   procedure Do_Nothing (R : in out Child) is
   begin
      R.F1 := 0;
   end Do_Nothing;

end Wrong_LSP;
