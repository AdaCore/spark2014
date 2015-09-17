package body Signals.Transient_Signals is

   ----------------------
   -- Transient_Signal --
   ----------------------

   protected body Transient_Signal is

      ----------
      -- Send --
      ----------

      procedure Send is
      begin
         Arrived := True; --Transient_Signal.Wait'Count > 0;
      end Send;

      ----------
      -- Wait --
      ----------

      entry Wait when Standard.True is
      begin
         Arrived := False;
      end Wait;

   end Transient_Signal;

   -----------
   -- Pulse --
   -----------

   protected body Pulse is

      ----------
      -- Send --
      ----------

      procedure Send is
      begin
         Arrived := True; --Pulse.Wait'Count > 0;
      end Send;

      ----------
      -- Wait --
      ----------

      entry Wait when Standard.True is
      begin
         Arrived := True; --Pulse.Wait'Count > 0;
      end Wait;

   end Pulse;

end Signals.Transient_Signals;
