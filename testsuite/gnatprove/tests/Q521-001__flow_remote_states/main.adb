with Ada.Text_IO; use Ada.Text_IO;
with PumpUnit;    use PumpUnit;
with Pump;        use Pump;

procedure Main is
begin
   PumpUnit.Initialize;
   PumpUnit.lift_nozel (1);
   PumpUnit.start_pumping;
   PumpUnit.stop_pumping;
   PumpUnit.replace_nozel;
   PumpUnit.pay;
end Main;
