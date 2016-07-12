package Test with SPARK_Mode is
   procedure Proc (X : in out Integer);
private
   pragma SPARK_Mode (Off);
   type Y is access Integer;
end Test;
