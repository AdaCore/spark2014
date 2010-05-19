--=head1 NAME
--
-- Steer_Cfg - steering fins configuration
--
--=head1 REVISION HISTORY
--
-- $Log: steer_cfg.ads,v $
-- Revision 1.2  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/08/31 13:14:31  adi
-- Added movement rate
--
-- Revision 1.1  2003/08/30 17:47:13  adi
-- Initial revision
--
--=cut

package Steer_Cfg
is
   --=head1 CONSTANTS
   --
   --=over 4

   --=item *
   --
   Max_Deflection : constant := 57;
   Min_Deflection : constant := -57;
   --
   --Max and min deflection of each fin, in degrees

   --=item *
   --
   Move_Rate : constant := 120;
   --
   --Maximum fin movement in degrees/sec

   --=back
   --
   --=head1 TYPES
   --
   --=over 4

   --=item *
   --
   type Fin_Angle is range
     Min_Deflection .. Max_Deflection;
   --
   --Range of deflections for a fin

   --=item *
   --
   type Fin is (Port,Starboard,Top,Bottom);
   --
   --Positions for a fin

   --=back
   --
   --=cut
end Steer_Cfg;

--=head1 NOTES
--
--This package provides basic configuration data for the C<Steer> steering
--package, including positions of fins and their deflection ranges.
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


