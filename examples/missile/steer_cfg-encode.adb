-- Steering fins encoding
--
-- $Log: steer_cfg-encode.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/31 19:25:44  adi
-- Initial revision
--
package body Steer_Cfg.Encode
is
   function Fin_Angle(F : Steer_Cfg.Fin_Angle)
                     return Bus.Word
   is begin
      return Bus.Word(F - Steer_Cfg.Fin_Angle'First);
   end Fin_Angle;

   function Fin(F : Steer_Cfg.Fin)
               return Bus.Word
   is
      Ans : Bus.Word;
   begin
      case F is
         when Steer_Cfg.Port =>
            Ans := 1;
         when Steer_Cfg.Starboard =>
            Ans := 2;
         when Steer_Cfg.Top =>
            Ans := 4;
         when Steer_Cfg.Bottom =>
            Ans := 8;
      end case;
      return Ans;
   end fin;

end Steer_Cfg.Encode;

