-- Warhead configuration
--
-- $Log: warhead_cfg-check.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/01 18:26:07  adi
-- Initial revision
--
--
with Warhead_Cfg;
--# inherit warhead_cfg;
package Warhead_Cfg.check
is
   procedure State(S : in String;
                   Expected, Actual : in Warhead_cfg.State);
end Warhead_Cfg.check;

