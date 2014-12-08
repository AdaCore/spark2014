package body Titi with
  SPARK_Mode
is
   procedure Get is
      -- Tmp : constant Integer := Log_In;
   begin
      Log_Size := Log_Size + 1;
      Log (Log_Size) := Log_In; -- Tmp
   end Get;
end Titi;
