--=head1 NAME
--
-- Warhead_Cfg - warhead configuration
--
--=head1 REVISION HISTORY
--
-- $Log: warhead_cfg.ads,v $
-- Revision 1.2  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/01 18:25:50  adi
-- Initial revision
--
--=cut

with Systemtypes;
--# inherit systemtypes;
package Warhead_Cfg
is

   --=head1 TYPES
   --
   --=over 4

   --=item *
   --
   type State is (Inactive,Awake,Armed,Final,Detonated);
   --
   --Basic state of the warhead.

   --=item *
   --
   type State_Code_Table is array (State) of
     Systemtypes.Unsigned16;
   --
   --Type for a lookup table on status codes

   --=item *
   --
   State_To_Code : constant State_Code_Table :=
     State_Code_Table'(Inactive  => 0,
                       Awake     => 16#54a3#,
                       Armed     => 16#9054#,
                       Final     => 16#7df2#,
                       Detonated => 16#386c#);
   --
   --Status codes for reporting on the bus

   --=back
   --
   --=head1 SUBPROGRAMS
   --
   --=over 4

   --=item *
   --
   function Code_To_State(C : Systemtypes.Unsigned16)
                         return State;
   --
   --Reverse lookup of a status code given a bus value.
   --Default for no match is C<Invalid>.

   --=item *
   --
   function Transition(Old_state : State;
                       New_Code  : Systemtypes.Unsigned16)
                      return State;
   --
   --Given the previous reported code and the new code,
   --update the state of the warhead I<if> the transition
   --is a valid one.  E.g. jumping from C<Awake> to C<Final> is
   --not valid.

   --=back
   --
   --=cut
end Warhead_Cfg;

--=head1 NOTES
--
--This package contains specific configuration information for
--the C<Warhead> package.  It provides information common for
--simulation and interfacing, specifying bus codes for the
--warhead states.
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



