-- Steering fins decoding
--
-- $Log: steer_cfg-decode.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/31 19:27:02  adi
-- Initial revision
--
--
with Bus,Steer_cfg;
--# inherit systemtypes,bus,steer_cfg;
package Steer_Cfg.decode
is
   function Fin_Angle(B : Bus.Word)
     return Steer_Cfg.Fin_Angle;

   function Fin(B : Bus.Word)
     return Steer_Cfg.Fin;

end Steer_Cfg.Decode;

