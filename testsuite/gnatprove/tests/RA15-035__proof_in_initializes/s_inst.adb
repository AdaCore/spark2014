with S_Gen;

procedure S_Inst (Y : in out Natural) with SPARK_Mode is
   C : constant Natural := Y;
   procedure S is new S_Gen (X => C);
begin
   null;
end S_Inst;
