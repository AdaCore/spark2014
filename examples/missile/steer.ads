--=head1 NAME
--
-- Steer - steering simulator
--
--=head1 REVISION HISTORY
--
-- $Log: steer.ads,v $
-- Revision 1.2  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.4  2003/08/31 20:06:35  adi
-- Corrected inheritance to encode and decode
--
-- Revision 1.3  2003/08/30 18:34:24  adi
-- Corrected annos for anticipated refinement relations
--
-- Revision 1.2  2003/08/30 18:12:07  adi
-- Read and set deflection for each individual fin
--
-- Revision 1.1  2003/08/30 17:48:24  adi
-- Initial revision
--
--=cut

with MeasureTypes,Clock,Steer_cfg;
use type Clock.Millisecond, Steer_Cfg.Fin_Angle;
--# inherit state_types, MeasureTypes, Bus, Rt1553,
--#         Clock, Clock_Utils, steer_cfg,
--#         IBIT, Bit_Machine, systemtypes,
--#         steer_cfg.encode, steer_cfg.decode;
package Steer
  --# own State;
  --# initializes State;
is
   -- 4 fins, each independent
   -- Deflect +- 1 radian
   -- 800ms max response to command

   subtype Angle is Steer_Cfg.Fin_Angle;
   subtype Fin is Steer_Cfg.Fin;

   --=head1 SUBPROGRAMS
   --
   --=over 4

   --=item *
   --
   procedure Cycle;
   --# global in out State;
   --#        in out Clock.Time;
   --#        in     Bus.Outputs;
   --#        in out Bus.Inputs;
   --# derives
   --#   State,
   --#   Clock.Time
   --#     from  State,
   --#           Bus.Outputs,
   --#           Clock.Time
   --#  &
   --#   Bus.Inputs
   --#     from  *,
   --#           Clock.Time,
   --#           State;
   --
   --Cycle the reading of data from the bus
   --and writing of data to the bus

   --=item *
   --
   procedure Set_Deflection
     (For_Fin   : in Fin;
      New_Angle : in Angle);
   --# global in out State, Clock.Time;
   --# derives
   --#   Clock.Time
   --#     from  *
   --#  &
   --#   State
   --#     from  *,
   --#           Clock.Time,
   --#           New_Angle,
   --#           For_Fin;
   --
   --Set the current steer deflection for the
   --fin C<For_Fin> to C<New_Angle>.

   --=item *
   --
   procedure Read_Deflection
     (For_Fin    : in Fin;
      This_Angle : out Angle);
   --# global in      State;
   --#         in out Clock.Time;
   --# derives
   --#   This_Angle
   --#     from  State,
   --#           For_Fin,
   --#           Clock.Time
   --#  &
   --#   Clock.Time
   --#     from  *;
   --
   --Read the current steer deflection for
   --fin C<For_Fin> into C<This_Angle>.

   --=item *
   --
   procedure Fail_Next_Bit;
   --# global in out State;
   --# derives State from *;
   --
   --Cause the next BIT to fail.

   --=item *
   --
   procedure Init;
   --# global out State;
   --#        in out Bus.Inputs;
   --# derives
   --#   State from
   --#  &
   --#   Bus.Inputs from *;
   --
   --Initialise the steering simulator.

   --=item *
   --
   procedure Command;
   --# derives;
   --
   --Test stub

   --=back
   --
   --=cut
end Steer;

--=head1 NOTES
--
--This package provides a simulator for steering the missile.
--Its control fin count and properties are set in
--package C<Steer_Cfg>.
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
