-- Dynamic drag computation
-- $Log: drag.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/12 18:11:40  adi
-- Initial revision
--
--

with Measuretypes;
use type measuretypes.meter;
use type measuretypes.meter_per_sec;
use type measuretypes.cm_per_sec_2;
--# inherit measuretypes, constants;
package Drag
is
   type Drag_Coefficient is range 1..1000;

   subtype pos_meter is measuretypes.meter range 0.. measuretypes.meter'last;
   subtype Pos_Meter_Per_Sec is Measuretypes.Meter_Per_Sec
     range 0 .. Measuretypes.Meter_Per_Sec'last;
   subtype cm_Per_Sec_2 is Measuretypes.cM_Per_Sec_2;

   procedure Calc_Drag(Profile    : in Drag_Coefficient;
                       Speed      : in Pos_Meter_Per_Sec;
                       Altitude   : in Pos_Meter;
                       Drag_force : out measuretypes.newton);
   --# derives Drag_force from Speed, Profile, Altitude;

   procedure testpoint;
   --# derives ;
end Drag;
