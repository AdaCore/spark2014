-- Maths functions on system types
--
-- $Log: systemtypes-maths.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/07 19:01:31  adi
-- Initial revision
--
--
with Systemtypes;
--# inherit systemtypes;
package SystemTypes.maths is

   function Sqrt(I : Systemtypes.Integer32)
     return Systemtypes.Integer32;

end SystemTypes.Maths;
