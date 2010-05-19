-- Destruct configuration
--
-- $Log: destruct_cfg-check.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/01 19:22:40  adi
-- Initial revision
--
--
with Test;
package body Destruct_Cfg.check
is
   procedure State(S : in String;
                   Expected, Actual : in Destruct_cfg.State)
   is
   begin
      Test.Align(S);
      if Expected = Actual then
         Test.Pass(" ");
      else
         Test.Fail(Destruct_Cfg.State'Image(Actual));
      end if;
   end State;

end Destruct_Cfg.check;

