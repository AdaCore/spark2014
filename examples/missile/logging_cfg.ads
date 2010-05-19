--=head1 NAME
--
-- Logging_Cfg - configuration for data logger
--
--=head1 REVISION HISTORY
--
-- $Log: logging_cfg.ads,v $
-- Revision 1.1  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
--
with
  Ada.Text_Io,
  Ada.Strings.Bounded,
  Test_Keywords;
package Logging_Cfg is
   --=head1 TYPES
   --
   --=over 4

   --=item *
   --
   type Log_Command is (Start,Stop,Enable,Disable);
   --
   --Possible commands that follow a C<Log> command.
   --C<Start> is followed by the name of a file in which to store the data.
   --C<Stop> is not followed by anything.
   --C<Enable> and C<Disable> are followed by an LRU name
   --such as C<Airspeed>.

   --=item *
   --
   subtype Lru_Name is Test_Keywords.Keyword
     range Test_Keywords.Barometer .. Test_Keywords.Missile;
   --
   --Names of the LRUs for which we can enable or disable logging

   --=item *
   --
   package Log_String_Ops is new 
     Ada.Strings.Bounded.Generic_Bounded_Length(Max => 256);
   subtype Log_String is Log_String_Ops.Bounded_String;
   --
   --Defines the type for strings to go in the logging buffer.
   --This is done by a generic instantiation of Bounded_String.

   --=item *
   --
   package Log_Io is new Ada.Text_Io.Enumeration_Io(Log_Command);
   --
   --Read in a log command.

   --=item *
   --
   package Lru_Io is new Ada.Text_Io.Enumeration_Io(Lru_Name);
   --
   --Read in an LRU name in the context of enabling/disabling logging

   --=back
   --
   --=cut
end Logging_Cfg;

--=head1 NOTES
--
--This package provides suitable types for text file based logging.
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



