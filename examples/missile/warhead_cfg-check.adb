-- Warhead configuration
--
-- $Log: warhead_cfg-check.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/01 18:26:55  adi
-- Initial revision
--
--
with Test;
package body Warhead_Cfg.check
is
   procedure State(S : in String;
                   Expected, Actual : in Warhead_cfg.State)
   is
   begin
      Test.Align(S);
      if Expected = Actual then
         Test.Pass(" ");
      else
         Test.Fail(Warhead_Cfg.State'Image(Actual));
      end if;
   end State;

end Warhead_Cfg.check;

