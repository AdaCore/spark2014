package body Trace_Test
is

   procedure Store_Values
   is
   begin
      Trace := Integer_Traces.Empty;
      Store.Init;

      for I in Integer range 1 .. 100
      loop
         Trace := Integer_Traces.Append (Trace, I);
         Store.Store_Element (I);
      end loop;
   end Store_Values;

end Trace_Test;
