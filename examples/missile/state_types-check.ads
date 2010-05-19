-- Checking for component states
--
-- $Log: state_types-check.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/08/22 18:28:08  adi
-- Added Radar
--
-- Revision 1.1  2003/08/17 14:34:22  adi
-- Initial revision
--
--
with State_types;
package State_Types.check is
   procedure Fuze(S : in String;
                  Expected, Actual : in State_Types.Fuze);
   procedure Radar(S : in String;
                  Expected, Actual : in State_Types.Radar);

end State_Types.Check;
