package body Dispatch_In_Contract with SPARK_Mode is

   procedure Incr (O : in out Root) is
   begin
      O.F1 := O.F1 + 1;
   end;

   procedure Incr (O : in out Child) is
   begin
      O.F1 := O.F1 + 1;
      O.F2 := O.F2 + 1;
   end;

   procedure Incr (O : in out Grand_Child) is
   begin
      O.F1 := O.F1 + 1;
      O.F2 := O.F2 + 1;
   end;

end Dispatch_In_Contract;
