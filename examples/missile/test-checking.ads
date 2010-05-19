-- Procedures to test general types.
-- You should normally create a 'Checks' public child package
-- for each significant package that declares types.
--
-- A good example of this is the Measuretypes package.
--
-- $Log: test-checking.ads,v $
-- Revision 1.3  2004/12/18 12:24:21  adi
-- Added margin parameter for integer comparison
--
-- Revision 1.2  2004/12/12 16:08:14  adi
-- Moved most type checking functions from test.Checking to Measuretypes.Checks as they should be
-- Added clarifications to compass.in as partial explanation of why errors appearing
--
--
--
with Systemtypes, clock;
use type
    Clock.Millisecond;
--# inherit Test, Systemtypes, clock;
package Test.Checking is
   procedure Bool(S         : in String;
                  Expected,Actual : in Boolean);
   --# global in out Test.State;
   --# derives Test.State from *, S, Expected, Actual;

   procedure time(S : in String;
                  Expected,Actual : in Clock.Millisecond);
   --# global in out Test.State;
   --# derives Test.State from *, S, Expected, Actual;

   procedure Unsigned16
     (S        : in String;
      Expected,
        Actual : in Systemtypes.Unsigned16;
      Margin   : in Systemtypes.Unsigned16);
   --# global in out Test.State;
   --# derives Test.State from *, S, Expected, Actual, Margin;

   procedure Signed16
     (S        : in String;
      Expected,
        Actual : in Systemtypes.Signed16;
      Margin   : in Systemtypes.Signed16);
   --# global in out Test.State;
   --# derives Test.State from *, S, Expected, Actual, Margin;

   -- Test parsing
   procedure Command;
   --# derives;
end Test.Checking;
