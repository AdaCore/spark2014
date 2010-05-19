-- The basic system types
-- Used by most other packages.
--
-- $Id: systemtypes.ads,v 1.1.1.1 2004/01/12 19:29:12 adi Exp $
--
-- $Log: systemtypes.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.4  2003/08/03 12:46:42  adi
-- Added Signed16
--
-- Revision 1.3  2003/08/02 19:14:40  adi
-- Added Integer32
--
-- Revision 1.2  2003/02/10 20:05:21  adi
-- Fixed base type of Unsigned32
--
-- Revision 1.1  2002/10/27 20:33:59  adi
-- Initial revision
--
--
package SystemTypes is

   subtype Integer32 is Long_Integer range -2147483648 .. 2147483647;
   subtype Unsigned32 is Natural range 0..2**31 -1;
   subtype Unsigned16 is Unsigned32 range 0..2**16-1;
   subtype Signed16 is Integer range -(2**15)..2**15-1;
   subtype Word is Unsigned16;
   subtype Unsigned8 is Unsigned32 range 0..2**8-1;
   subtype Byte is Unsigned8;

end SystemTypes;
