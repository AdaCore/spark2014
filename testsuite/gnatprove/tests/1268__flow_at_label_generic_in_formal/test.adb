with Generic_Snapshot;

procedure Test (Early, Late : Integer; Output : out Integer)
with
  Depends => (Output => Early, null => Late)
is
   package Instance is new Generic_Snapshot (Initial => Early);
begin
   Instance.Read_Captured (Later => Late, Output => Output);
end Test;
