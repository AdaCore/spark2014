package body Spark_Mode_Off
is
   procedure P
     with Spark_Mode => Off
   is
   begin
      null;
   end;
end;
