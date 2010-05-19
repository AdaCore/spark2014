-- Steering fins decoding
--
-- $Log: steer_cfg-decode.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.3  2003/08/31 21:03:13  adi
-- Removed unnecessary type conversion
--
-- Revision 1.2  2003/08/31 20:40:25  adi
-- Fixed constraint err in fin decoding
--
-- Revision 1.1  2003/08/31 19:44:57  adi
-- Initial revision
--
--
package body Steer_Cfg.Decode
is

   function Fin_Angle(B : Bus.Word)
     return Steer_Cfg.Fin_Angle
   is
      T : Integer;
   begin
      T := B;
      T := Integer(Steer_Cfg.Fin_Angle'First) + T;
      return Steer_Cfg.Fin_Angle(T);
   end Fin_Angle;

   function Fin(B : Bus.Word)
     return  Steer_Cfg.Fin
   is
      Ans : Steer_Cfg.fin;
   begin
      if B = 1 then
         Ans := Steer_Cfg.Port;
      elsif B = 2 then
         Ans := Steer_Cfg.Starboard;
      elsif B = 4 then
         Ans := Steer_Cfg.top;
      elsif B = 8 then
         Ans := Steer_Cfg.bottom;
      else
         Ans := Steer_Cfg.Port;
      end If;
      return Ans;
   end fin;

end Steer_Cfg.Decode;

