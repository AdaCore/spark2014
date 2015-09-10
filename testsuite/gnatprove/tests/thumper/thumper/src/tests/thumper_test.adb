---------------------------------------------------------------------------
-- FILE    : thumper_test.adb
-- SUBJECT : Main procedure of the Thumper unit test program.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with AUnit.Run;
with AUnit.Reporter.Text;

with Primary_Suite;

procedure Thumper_Test is
   procedure Run is new AUnit.Run.Test_Runner(Primary_Suite.Suite);
   Reporter : AUnit.Reporter.Text.Text_Reporter;
begin
   Run(Reporter);
end Thumper_Test;
