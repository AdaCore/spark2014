package body Test is
   type X is access Integer;

   procedure Proc (X : in out Integer) with SPARK_Mode is
   begin
      X := X + 1;
   end Proc;
end Test;
