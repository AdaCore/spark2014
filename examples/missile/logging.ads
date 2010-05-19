--=head1 NAME
--
-- Logging - data logger
--
--=head1 REVISION HISTORY
--
-- $Log: logging.ads,v $
-- Revision 1.1  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
--
with
  Ada.Text_Io,
  Logging_Cfg,
  Test_Keywords;
use type Logging_Cfg.Log_Command;
use type Test_Keywords.Keyword;
package Logging is
   --=head1 SUBPROGRAMS
   --
   --=over 4

   --=item *
   --
   procedure Finish_Logging;
   --
   --If logging is active, stop it and close the file.  No effect
   --if logging is inactive.

   --=item *
   --
   procedure Start_Logging(Filename : in String);
   --
   --Stop any active logging, then open a new log in the
   --file C<Filename>.

   --=item *
   --
   procedure Log;
   --
   --If logging is active, dump each LRU's log data into the log file.

   --=item *
   --
   procedure Process_Logging;
   --
   --Read the rest of a log command off the command line, and act on
   --it.  Expect a C<Log_Command> to start the line.

   --=back
   --
   --=cut
end Logging;

--=head1 NOTES
--
--This package provides simple facilities for text file based logging.
--
--=head1 WORK REMAINING
--
--Currently only implements logging for C<Airspeed>.  As we add logging
--facilities to other LRUs, add calls to them in the body of this
--package.
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



