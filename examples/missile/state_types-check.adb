-- Checking for component states
--
-- $Log: state_types-check.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/08/22 18:28:01  adi
-- Added radar
--
-- Revision 1.1  2003/08/17 14:34:26  adi
-- Initial revision
--
--
with Ada.Text_Io,test;
package body State_Types.check is
   procedure Fuze(S : in String;
                  Expected, Actual : in State_Types.Fuze)
   is begin
      Test.Align(S);
      if Expected = Actual then
         Test.Pass(" ");
      else
         Test.Fail(State_Types.Fuze'Image(Actual));
      end if;
   end Fuze;

   procedure radar(S : in String;
                  Expected, Actual : in State_Types.radar)
   is begin
      Test.Align(S);
      if Expected = Actual then
         Test.Pass(" ");
      else
         Test.Fail(State_Types.radar'Image(Actual));
      end if;
   end radar;

end State_Types.Check;
