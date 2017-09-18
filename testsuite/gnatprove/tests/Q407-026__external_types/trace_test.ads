with Traces; pragma Elaborate_All (Traces);
with Store;

package Trace_Test
is
   package Integer_Traces is new Traces (Integer);

   Trace : Integer_Traces.Trace with Ghost;

   procedure Store_Values
   with
     Global => (Output => (Store.State, Trace)),
     Depends => ((Store.State, Trace) => null),
     Post =>
       (for all C in Trace =>
          (if not Integer_Traces.Is_First (Trace, C)
           then
             Integer_Traces.Element (Trace, C) =
             Integer_Traces.Element (Trace, Integer_Traces.Previous (Trace, C)) + 1));

end Trace_Test;
