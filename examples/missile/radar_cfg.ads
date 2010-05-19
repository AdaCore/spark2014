-- Radar configuration
--
-- $Log: radar_cfg.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.5  2003/08/25 19:35:09  adi
-- Added encode and decode of sector
--
-- Revision 1.4  2003/08/25 14:04:07  adi
-- Updated for use of angle_ops
--
-- Revision 1.3  2003/08/25 13:29:05  adi
-- Added max_detect_range
--
-- Revision 1.2  2003/08/22 18:20:53  adi
-- Changed sector to 40 millirads wide
--
-- Revision 1.1  2003/08/18 18:20:30  adi
-- Initial revision
--
--
with MeasureTypes,systemtypes;
--# inherit Measuretypes, measuretypes.angle_ops,
--#  systemtypes;
package Radar_Cfg
is
   Max_Detect_Range : constant Measuretypes.Meter := 50_000;

   type Sector_Range is range -20..20;

   Sector_Angle : constant Measuretypes.Millirad
     := Measuretypes.Forty_Millirads;

   function Sector_To_Millirad(S : Sector_Range)
                              return Measuretypes.Millirad;

   function Encode_Sector(S : Sector_Range) return
     Systemtypes.Unsigned16;

   function decode_Sector(B : Systemtypes.unsigned16) return
     Sector_Range;

end Radar_Cfg;

