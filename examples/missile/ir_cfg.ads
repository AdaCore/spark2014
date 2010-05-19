-- IR configuration
--
-- $Log: ir_cfg.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/26 18:27:27  adi
-- Initial revision
--
--
with MeasureTypes,systemtypes;
--# inherit Measuretypes, measuretypes.angle_ops,
--#  systemtypes;
package Ir_Cfg
is
   Max_Detect_Range : constant Measuretypes.Meter := 30_000;

   type Sector_Range is range -12..12;

   Sector_Angle : constant Measuretypes.Millirad
     := Measuretypes.Hundred_Millirads;

   function Sector_To_Millirad(S : Sector_Range)
                              return Measuretypes.Millirad;

   function Encode_Sector(S : Sector_Range) return
     Systemtypes.Unsigned16;

   function decode_Sector(B : Systemtypes.unsigned16) return
     Sector_Range;

end ir_Cfg;

