package Handlers with SPARK_Mode is

   type No_Param_Proc is access procedure with
     Annotate => (GNATprove, Handler);

   type No_Param_Fun is access function return Boolean with
     Annotate => (GNATprove, Handler);

   V : Boolean := True; -- V is not synchronized, it should not be accessed by handlers

   procedure P;
   function F return Boolean with Side_Effects;

end Handlers;
