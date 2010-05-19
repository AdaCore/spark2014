--=head1 NAME
--
-- Warhead - warhead simulator
--
--=head1 REVISION HISTORY
--
-- $Log: warhead.ads,v $
-- Revision 1.2  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/09/01 18:56:47  adi
-- Added use type for state
--
-- Revision 1.1  2003/09/01 18:25:18  adi
-- Initial revision
--
--=cut

with Clock,Warhead_cfg;
use type Clock.Millisecond, Warhead_Cfg.state;
--# inherit state_types, Bus, Rt1553,
--#         Clock, Clock_Utils, warhead_cfg,
--#         IBIT, Bit_Machine, systemtypes;
package Warhead
  --# own State;
  --# initializes State;
is
   -- Renaming of warhead state type
   subtype Stage is Warhead_Cfg.State;

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
   --# &
   --#   Bus.Inputs
   --#     from  *,
   --#           Clock.Time,
   --#           State
   --#  ;
   --
   --Cycle the reading of data from the bus
   --and writing of data to the bus

   --=item *
   --
   procedure Set_Stage(New_Stage : in Stage);
   --# global in out State, Clock.Time;
   --# derives
   --#   Clock.Time
   --#     from  *
   --#  &
   --#   State
   --#     from  *,
   --#           Clock.Time,
   --#           New_Stage;
   --
   --Set the current code exchange stage level.
   --This determines what state the warhead is allowed
   --to be in; it may implement minimum times between
   --stages (e.g. 2 seconds between arming and detonation).

   --=item *
   --
   procedure Read_Stage(This_Stage : out Stage);
   --# global in     State;
   --# derives
   --#   This_Stage
   --#     from  State;
   --
   --Read the current code exchange stage.

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
   --# global    out State;
   --#        in out Bus.Inputs;
   --# derives
   --#   State
   --#     from
   --#  &
   --#   Bus.Inputs
   --#     from  *;
   --
   --Initialise the warhead.

   --=item *
   --
   procedure Command;
   --# derives;
   --
   --Test stub

   --=back
   --
   --=cut
end Warhead;

--=head1 NOTES
--
--This package provides a simulator of a warhead for a missile.
--It implements communication over the system bus and certain
--control aspects such as minimum timings between state changes.
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

