package Handlers with SPARK_Mode is

   type No_Param_Proc is access procedure with
     Annotate => (GNATprove, Handler);

   type No_Param_Fun is access function return Integer with
     Annotate => (GNATprove, Handler);

   V : Integer := 12; -- V is not synchronized, it should not be accessed by handlers

   procedure P_Incr with
     Pre => V < Integer'Last;

   function F_Incr return Integer with
     Side_Effects,
     Pre => V < Integer'Last;

end Handlers;
