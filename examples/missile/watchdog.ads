--=head1 NAME
--
-- Watchdog - watchdog timer
--
--=head1 REVISION HISTORY
--
-- $Log: watchdog.ads,v $
-- Revision 1.2  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/02/09 19:48:11  adi
-- Initial revision
--
--
--=cut

--# inherit Clock;
package Watchdog
  --# own State;
  --# initializes State;
is
   --=head1 TYPES
   --
   --=over 4
   --
   --=cut

   --=item *
   --
   type Timer_Check is (Timeout,OK,Invalid);
   --
   --A status code to see whether the current watchdog has
   --timed out (C<Timeout>), has broken (C<Invalid>) or is
   --all right (C<OK>).
   --
   --=cut

   --=back
   --
   --=head1 SUBPROGRAMS
   --
   --=over 4

   --=item *
   --
   procedure Reset;
   --# global    out State;
   --#        in out Clock.Time;
   --# derives
   --#   State,
   --#   Clock.Time
   --#     from  Clock.Time;
   --
   --The public watchdog reset procedure.  Must be called
   --periodically to stop the system being reset.

   --=item *
   --
   procedure Check_Timeout(V : out Timer_Check);
   --# global in     State;
   --#        in out Clock.Time;
   --# derives
   --#   Clock.Time
   --#     from *
   --# &
   --#   V
   --#   from  State,
   --#         Clock.Time;
   --
   --Check to see what state the watchdog is in currently.

   --=back
   --
   --=cut
end Watchdog;

--=head1 NOTES
--
--This package is a simple implementation of a watchdog timer
--interface.  It tracks the time between resets, and if this is
--too long (750ms, configured in the package body) it will
--indicate a Timeout on the subsequent checks.
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

