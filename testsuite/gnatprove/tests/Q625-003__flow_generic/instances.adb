package body Instances
with SPARK_Mode => Off
is

   procedure A_Null_Procedure (A : in out Integer)
   is
   begin
      null;
   end A_Null_Procedure;

end Instances;
