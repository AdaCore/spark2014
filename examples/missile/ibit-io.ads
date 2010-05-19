-- IBIT types I/o
--
-- $Log: ibit-io.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/10 20:04:34  adi
-- Initial revision
--
--
with Ada.Text_Io,Ibit;
package IBIT.io is

   package Phase_Io is new
     Ada.Text_Io.Enumeration_Io(Ibit.Phase);

end IBIT.io;

