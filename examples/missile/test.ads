-- Test harness auxiliary
-- $Id: test.ads,v 1.1.1.1 2004/01/12 19:29:12 adi Exp $
--
-- $Log: test.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.4  2003/02/12 23:15:57  adi
-- Added Comment function
--
-- Revision 1.3  2003/02/11 23:15:34  adi
-- Added Pass and Fail operations
--
-- Revision 1.2  2003/02/11 21:09:34  adi
-- Simplified main test body
--
-- Revision 1.1  2003/02/03 19:59:15  adi
-- Initial revision
--
--
package Test
  --# own State;
  --# initializes State;
is
   procedure Align(S : in String);
   --# global in out State;
   --# derives State from *, S;

   procedure Pass(S : in String);
   --# global in out State;
   --# derives State from *, S;

   procedure Fail(S : in String);
   --# global in out State;
   --# derives State from *, S;

   procedure Section(S : in String);
   --# global in out State;
   --# derives State from *, S;

   procedure Comment(S : in String);
   --# global in out State;
   --# derives State from *, S;

   procedure Done;
   --# derives;

   function Passes return Natural;
   --# global State;

   function Fails return Natural;
   --# global State;
end Test;
