-- IBIT checking
--
-- $Log: ibit-checks.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/10 20:04:41  adi
-- Initial revision
--
--
with Test.Checking,Test,ibit;
package IBIT.checks is

   procedure Phase(S : in String;
                   Expected, Actual : in Ibit.Phase);
   --# global in out test.state;
   --# derives test.state from *, expected,actual,s;

end IBIT.checks;

