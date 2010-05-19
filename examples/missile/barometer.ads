--=head1 NAME
--
-- Barometer - barometer simulator code
--
--=head1 REVISION HISTORY
--
-- $Log: barometer.ads,v $
-- Revision 1.2  2004/12/19 15:53:40  adi
-- Added POD to airspeed, barometer, bc1553
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.6  2003/08/06 20:41:22  adi
-- Use bit_machine
--
-- Revision 1.5  2003/02/19 19:04:44  adi
-- Details for Command proc
--
-- Revision 1.4  2003/02/12 23:11:25  adi
-- Added init routine
--
-- Revision 1.3  2003/02/11 20:49:31  adi
-- Minor fixes to withs and inherits
--
-- Revision 1.2  2003/02/10 20:06:40  adi
-- SPARKs after body implemented
--
-- Revision 1.1  2003/02/09 20:58:42  adi
-- Initial revision
--
--=cut
with MeasureTypes,Clock;
use type MeasureTypes.Meter;
use type MeasureTypes.Meter_Per_Sec;
use type Clock.Millisecond;
--# inherit MeasureTypes, Bus, Rt1553,
--#         Clock, Clock_Utils, SystemTypes,
--#         IBIT, Bit_Machine;
package Barometer
  --# own State;
  --# initializes State;
is
   -- Type renamings for brevity
   subtype Meter is MeasureTypes.Meter;
   subtype Meter_Per_Sec is MeasureTypes.Meter_Per_Sec;

   --=head1 SUBPROGRAMS
   --
   --=over 4
   --
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
   procedure Set_Altitude_Profile(Height : in Meter;
                                  DZ     : in Meter_Per_Sec);
   --# global in out State, Clock.Time;
   --# derives Clock.Time from * &
   --#         State from *, Clock.Time, Height, DZ;
   --
   --Set the current altitude profile and vertical velocity
   --to C<Height> and C<DZ> respectively.
   --

   --=item *
   --
   procedure Read_Altitude(Height : out Meter);
   --# global in     State;
   --#        in out Clock.Time;
   --# derives Clock.Time from * &
   --#         Height from State, Clock.Time;
   --
   --Read the current altitude as C<Height>
   --

   --=item *
   --
   procedure Fail_Next_Bit;
   --# global in out State;
   --# derives State from *;
   --
   --Cause the next BIT to fail.
   --

   --=item *
   --
   procedure Init;
   --# global out State;
   --#        in out Bus.Inputs;
   --# derives State from &
   --#         Bus.Inputs from *;
   --
   --Initialise the barometric simulator.
   --

   --=item *
   --
   procedure Command;
   --# derives;
   --
   --Test harness point.  Reads controlling keywords from
   --standard input, and adjusts barometer sim state accordingly.
   --

   --=back
   --
   --=cut
end Barometer;

--=head1 NOTES
--
--This package provides a simulator of a barometric pressure
--measuring device for the
--system.  It allows the testing harness to set a current altitude and
--constant vertical speed, and will extrapolate to calculate new altitude
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

