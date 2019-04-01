package body Repro with SPARK_Mode is

   procedure Proc (K : Kind) with Pre => True is
   begin
      null;
   end Proc;

   procedure Process (Arg : R) is
   begin
      for Ids in Arg.X'First .. Arg.X'Last loop
         for Diff in 1 .. Arg.X(Ids).S.Len loop
            Proc (Arg.X(Ids).S.M(Diff).K);
         end loop;
      end loop;
   end Process;

end Repro;
