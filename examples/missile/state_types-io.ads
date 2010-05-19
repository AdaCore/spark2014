-- I/O for component states
--
-- $Log: state_types-io.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/08/22 18:28:51  adi
-- Added Radar
--
-- Revision 1.1  2003/08/17 14:34:43  adi
-- Initial revision
--
--
with State_Types;
with Ada.Text_Io;
package State_Types.io is
   package Fuze_Io is new
     Ada.Text_Io.Enumeration_Io(Fuze);
   package radar_Io is new
     Ada.Text_Io.Enumeration_Io(radar);

end State_Types.io;
