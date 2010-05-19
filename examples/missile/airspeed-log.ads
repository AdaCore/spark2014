--=head1 NAME
--
-- Airspeed.Log - logging information from Airspeed package
--
--=head1 REVISION HISTORY
--
-- $Log: airspeed-log.ads,v $
-- Revision 1.1  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
--
--=cut

--# inherit Airspeed,Clock;
with Logging_Cfg;
package Airspeed.Log
is
   --=head1 SUBPROGRAMS
   --
   --=over 4

   --=item *
   --
   function Header return Logging_Cfg.Log_String;
   --
   --Return a string giving the header information for each column of
   --the C<Airspeed> logging data

   --=item *
   --
   procedure Data(Ans : out Logging_Cfg.Log_String);
   --# global in Airspeed.State;
   --#        in out Clock.Time;
   --# derives
   --#    Ans from Airspeed.State, Clock.Time
   --#  &
   --#    Clock.Time from *;
   --
   --Return a string representing the internal state information of the
   --C<Airspeed> package state.

   --=back
   --
   --=cut

end Airspeed.Log;

--=head1 NOTES
--
--This package allows external view of the internal Airspeed data
--in text form.  This is primarily used by package C<Logging>.
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
