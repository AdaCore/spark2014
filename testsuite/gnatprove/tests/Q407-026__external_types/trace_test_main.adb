with Trace_Test;
with Store;

procedure Trace_Test_Main
with
  Global => (Output => (Store.State, Trace_Test.Trace)),
  Depends => ((Store.State, Trace_Test.Trace) => null)
is
begin
   Trace_Test.Store_Values;
end;
