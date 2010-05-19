-- Checking of miscellaneous types
--
-- $Log: test-checking.adb,v $
-- Revision 1.3  2004/12/18 12:24:21  adi
-- Added margin parameter for integer comparison
--
-- Revision 1.2  2004/12/12 16:08:14  adi
-- Moved most type checking functions from test.Checking to Measuretypes.Checks as they should be
-- Added clarifications to compass.in as partial explanation of why errors appearing
--
--
--
with Ada.Text_Io;
package body Test.Checking is
   procedure Bool(S         : in String;
                  Expected, Actual : in Boolean)
   is
   begin
      Test.Align(S);
      if Expected = Actual then
         Test.Pass(" ");
      else
         Test.Fail(Boolean'Image(Actual));
      end if;
   end Bool;

   procedure Time(S : in String;
                    Expected,
                      Actual : in Clock.millisecond)
   is begin
      Test.Align(S);
      if Expected = Actual then
         Test.Pass(" ");
      else
         Test.Fail("E=" & Clock.Millisecond'Image(Expected) &
                   "ms, A=" & Clock.millisecond'Image(Actual) &
                   "ms");
      end if;
   end time;

   procedure Signed16
     (S        : in String;
      Expected,
        Actual : in Systemtypes.Signed16;
      Margin   : in Systemtypes.Signed16)
   is begin
      Test.Align(S);
      if Expected = Actual then
         Test.Pass(" ");
      elsif (Expected > Actual and then (Expected - Actual <= Margin)) or
        (Actual > Expected and then (Actual - Expected <= Margin)) then
         Test.Pass(" (within margin)");
      else
         Test.Fail("E=" & Systemtypes.Signed16'Image(Expected) &
                   ", A=" & Systemtypes.Signed16'Image(Actual));
      end if;
   end Signed16;

   procedure Unsigned16
     (S        : in String;
      Expected,
        Actual : in Systemtypes.Unsigned16;
      Margin   : in Systemtypes.Unsigned16)
   is begin
      Test.Align(S);
      if Expected = Actual then
         Test.Pass(" ");
      elsif (Expected > Actual and then (Expected - Actual <= Margin)) or
        (Actual > Expected and then (Actual - Expected <= Margin)) then
         Test.Pass(" (within margin)");
      else
         Test.Fail("E=" & Systemtypes.Unsigned16'Image(Expected) &
                   ", A=" & Systemtypes.Unsigned16'Image(Actual));
      end if;
   end Unsigned16;

   -- Process miscellaneous commands to the test checking
   procedure Command is
   begin
      null;
   end Command;
end Test.Checking;
