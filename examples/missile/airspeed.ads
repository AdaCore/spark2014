--=head1 NAME
--
-- Airspeed - airspeed simulator code
--
--=head1 REVISION HISTORY
--
-- $Log: airspeed.ads,v $
-- Revision 1.3  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
-- Revision 1.2  2004/12/19 15:53:40  adi
-- Added POD to airspeed, barometer, bc1553
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/08/08 20:45:13  adi
-- Corrected minor annos
--
-- Revision 1.1  2003/08/06 21:02:09  adi
-- Initial revision
--
--
--=cut
with MeasureTypes,Clock,BIT_Machine;
use type MeasureTypes.Meter;
use type MeasureTypes.Meter_Per_Sec;
use type Measuretypes.Cm_Per_Sec_2;
use type Clock.Millisecond;
--# inherit MeasureTypes, Bus, Rt1553,
--#         Clock, Clock_Utils, SystemTypes,
--#         IBIT, Bit_Machine;
package Airspeed
  --# own State;
  --# initializes State;
is
   -- Type renamings for brevity
   subtype Meter_Per_Sec is MeasureTypes.Meter_Per_Sec;
   subtype Meter_Per_Sec_2 is Measuretypes.Meter_Per_Sec_2;
   subtype Cm_Per_Sec_2 is Measuretypes.Cm_Per_Sec_2;

   --=head1 SUBPROGRAMS
   --
   --=over4

   --=item *
   --
   procedure Cycle;
   --# global in out State;
   --#        in out Clock.Time;
   --#        in Bus.Outputs;
   --#        in out Bus.Inputs;
   --# derives State from *, Bus.Outputs &
   --#        Bus.Inputs from *, Clock.Time, State &
   --#        Clock.Time from *;
   --
   --Cycle the reading of data from the bus
   --and writing of data to the bus
   --

   --=item *
   --
   procedure Set_Airspeed_Profile(Speed : in Meter_Per_Sec;
                                  Accel : in cm_Per_Sec_2);
   --# global in out State, Clock.Time;
   --# derives Clock.Time from * &
   --#         State from *, Clock.Time, Speed, Accel;
   --
   --Set the current airspeed and acceleration
   --vertical velocity to C<Speed> and C<Accel> respectively.
   --When the system next queries airspeed across the bus,
   --the airspeed will be extrapolated from C<Speed> given
   --an assumed acceleration of C<Accel>.
   --

   --=item *
   --
   procedure Read_Airspeed(Speed : out Meter_Per_Sec);
   --# global in     State;
   --#        in out Clock.Time;
   --# derives Clock.Time from * &
   --#         Speed from State, Clock.Time;
   --
   --Read the current airspeed as C<Speed>.  This will extrapolate
   --from the last-set airspeed at the last-set time by adding
   --the appropriate fraction of the last-set acceleration.
   --

   --=item *
   --
   function Read_Accel return Cm_Per_Sec_2;
   --# global in State;
   --
   --Return the last-set acceleration value

   --=item *
   --
   function Read_BIT_Status return BIT_Machine.Machine;
   --# global in State;
   --
   --Return the current BIT status.

   --=item *
   --
   procedure Fail_Next_Bit;
   --# global in out State;
   --# derives State from *;
   --
   --Cause the next BIT request by the system to fail.
   --

   --=item *
   --
   procedure Init;
   --# global out State;
   --#        in out Bus.Inputs;
   --# derives State from &
   --#         Bus.Inputs from *;
   --
   --Initialise the airspeed simulator to zero values.
   --

   --=item *
   --
   procedure Command;
   --# derives;
   --
   --Test stub
   --

   --=back
   --
   --=cut
end Airspeed;

--=head1 NOTES
--
--This package provides a simulator of an airspeed measuring device for the
--system.  It allows the testing harness to set a current airspeed and
--constant acceleration, and will extrapolate to calculate new airspeed
--at each future read.  It also allows very basic control over failure of
--built-in test run requests.
--
--=head1 AUTHOR
--
--Adrian J. Hilton.  Home web page at L<http://www.suslik.org/>
--
--=head1 LICENSE
--
--Copyright (C) 2003-2005, Adrian J. Hilton
--
--This program is free software; you can redistribute it and/or modify
--it under the terms of the GNU General Public License as published by
--the Free Software Foundation; either version 2 of the License, or
--(at your option) any later version.
--
--This program is distributed in the hope that it will be useful,
--but WITHOUT ANY WARRANTY; without even the implied warranty of
--MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
--GNU General Public License for more details.
--
--You should have received a copy of the GNU General Public License
--along with this program; if not, write to the Free Software
--Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
--
--=cut
