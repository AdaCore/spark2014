procedure Test (X, Y : Boolean) with SPARK_Mode
is
   procedure Proc is
   begin
      <<L>>
      null;
   end;
begin
   Proc;
   Proc;
   pragma Assert (X = Y);  --  unprovable VC to trigger gnatwhy3 execution
end;
