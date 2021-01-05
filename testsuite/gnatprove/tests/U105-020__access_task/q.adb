package body Q with SPARK_Mode is
   procedure Proc is
   begin
      X.all := not X.all;
   end Proc;
end Q;
