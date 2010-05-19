-- IR configuration
--
-- $Log: ir_cfg.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/26 18:27:23  adi
-- Initial revision
--
--
with Measuretypes.Angle_Ops;
package body Ir_Cfg
is
   subtype Integer32 is Systemtypes.Integer32;

   function Sector_To_Millirad(S : Sector_Range)
                              return Measuretypes.Millirad
   is
      Ans : Measuretypes.Millirad;
   begin
      Ans := Measuretypes.Angle_Ops.Mul(Orig_Angle => Sector_angle,
                                        Mult  => Integer(S));
      return Ans;
   end Sector_To_Millirad;


   function Encode_Sector(S : Sector_Range) return
     Systemtypes.Unsigned16
   is
   begin
      return Systemtypes.Unsigned16(S - Sector_Range'First);
   end Encode_Sector;

   function decode_Sector(B : Systemtypes.unsigned16) return
     Sector_Range
   is begin
       return Sector_Range(Integer32(Sector_Range'First) + Integer32(B));
   end Decode_Sector;

end ir_Cfg;

