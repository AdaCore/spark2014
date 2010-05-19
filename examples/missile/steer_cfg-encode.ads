-- Steering fins encoding
--
-- $Log: steer_cfg-encode.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/31 19:13:28  adi
-- Initial revision
--
--
with Bus,Steer_cfg;
--# inherit systemtypes,bus,steer_cfg;
package Steer_Cfg.Encode
is
   function Fin_Angle(F : Steer_Cfg.Fin_Angle)
     return Bus.Word;

   function Fin(F : Steer_Cfg.Fin)
     return Bus.Word;

end Steer_Cfg.Encode;

