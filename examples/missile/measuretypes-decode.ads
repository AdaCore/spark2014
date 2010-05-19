-- Bus decoding for measuretypes
--
-- $Log: measuretypes-decode.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.3  2003/09/01 18:19:41  adi
-- Added Newton
--
-- Revision 1.2  2003/08/27 21:01:20  adi
-- Added kelvin
--
-- Revision 1.1  2003/08/25 14:34:49  adi
-- Initial revision
--
--
with MeasureTypes, bus;
--# inherit measuretypes, bus,systemtypes;
package Measuretypes.decode is
   function Kelvin(B : Bus.Word) return Measuretypes.Kelvin;

   function Newton(Lo, Hi : Bus.Word) return Measuretypes.Newton;

   procedure Meter(M : out Measuretypes.Meter;
                   Lo, Hi : in bus.Word);
   --# derives m from lo, hi;

   function Meter_Single(B : Bus.Word)
     return Measuretypes.meter;

   function Meter_Per_Sec(B : Bus.Word)
     return Measuretypes.Meter_Per_Sec;

   function Bit4_Array(B : Bus.Word)
     return Measuretypes.Bit4_Array;

end Measuretypes.decode;
