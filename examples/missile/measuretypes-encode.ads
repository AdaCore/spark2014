-- Bus encoding for measuretypes
--
-- $Log: measuretypes-encode.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.4  2003/09/01 18:23:40  adi
-- Updated for Newton
--
-- Revision 1.3  2003/08/27 20:42:36  adi
-- Added Kelvin
--
-- Revision 1.2  2003/08/25 13:32:37  adi
-- Added Bit4_array
--
-- Revision 1.1  2003/08/24 19:12:25  adi
-- Initial revision
--
--
with MeasureTypes, bus;
--# inherit measuretypes, bus,systemtypes;
package Measuretypes.encode is
   function Kelvin(K : Measuretypes.Kelvin) return Bus.Word;

   procedure Newton(N : in Measuretypes.Newton;
                    Lo, Hi : out Bus.Word);
   --# derives lo, hi from n;

   procedure Meter(M : in Measuretypes.Meter;
                   Lo, Hi : out bus.Word);
   --# derives lo, hi from m;

   function Meter_Single(M : Measuretypes.Meter;
                         R : Measuretypes.Meter)
     return Bus.Word;

   procedure Meter_Per_Sec(V : in Measuretypes.Meter_Per_Sec;
                           W : out bus.Word);
   --# derives W from V;

   function Bit4_Array(A : Measuretypes.Bit4_Array)
     return Bus.Word;

end Measuretypes.encode;
