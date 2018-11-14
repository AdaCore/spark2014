
with P_Gen;
procedure P_Inst (Y : in out Natural) with SPARK_Mode is
   C : constant Natural := Y;
   package P is new P_Gen (X => C);
begin
   null;
end P_Inst;
