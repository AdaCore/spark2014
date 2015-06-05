package body Repro
--  with SPARK_Mode
is
   procedure  exigence(sortie1:  in out boolean;
                       sortie2 : in out boolean) with SPARK_Mode
   is
   begin
      sortie1 := true;
      sortie2 := true;
   end exigence;
end Repro;
