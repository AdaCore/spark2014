-- Destruct configuration
--
-- $Log: destruct_cfg-check.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/01 19:22:43  adi
-- Initial revision
--
--
with Destruct_Cfg;
--# inherit destruct_cfg;
package Destruct_Cfg.check
is
   procedure State(S : in String;
                   Expected, Actual : in Destruct_cfg.State);
end Destruct_Cfg.check;

