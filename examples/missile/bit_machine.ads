--=head1 NAME
--
-- bit_machine - BIT machine for components
--
--=head1 REVISION HISTORY
--
-- $Log: bit_machine.ads,v $
-- Revision 1.2  2004/12/20 18:21:31  adi
-- Added POD for bit_machine.ads
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
-- Revision 1.4  2003/09/10 20:03:12  adi
-- Added Ticks counter
--
-- Revision 1.3  2003/08/06 20:38:06  adi
-- Corrected constant defn
--
-- Revision 1.2  2003/08/06 20:29:53  adi
-- Split out of Compass/Barometer
--
-- Revision 1.1  2003/08/05 22:06:17  adi
-- Initial revision
--
--=cut
with SystemTypes,Bus,IBIT;
--# inherit Bus,SystemTypes,IBIT;
package BIT_Machine
is
   --=head1 TYPES
   --
   --=over 4
   --
   --=cut

   --=item *
   --
   type Machine is private;
   Initial_Machine : constant Machine;
   --
   --Private type of a machine that is instantiated for each subsystem
   --wanting a BIT machine
   --
   --=cut

   --=back
   --
   --=head1 SUBPROGRAMS
   --
   --=over 4

   --=item *
   --
   procedure Create
     (Ticks_To_Complete : in     Systemtypes.Unsigned16;
      State             :    out Machine);
   --# derives State from Ticks_To_Complete;
   --
   --Create a BIT machine C<State> which will take
   --C<Ticks_To_Complete> BIT ticks until the BIT reports success.
   --

   --=item *
   --
   function Phase(State : Machine)
                 return IBIT.Phase;
   --
   --Get the current BIT phase for machine C<State>.
   --

   --=item *
   --
   function Machine_Ticks(State : Machine)
                         return Systemtypes.Unsigned16;
   --
   --Get the current number of ticks for machine C<State>.
   --

   --=item *
   --
   procedure Init(State : in out Machine);
   --# derives State from *;
   --
   --Kick off a BIT for machine C<State>
   --

   --=item *
   --
   procedure Halt(State : in out Machine);
   --# derives State from *;
   --
   --Stop a BIT in progress on machine C<State>
   --

   --=item *
   --
   procedure Step(State : in out Machine);
   --# derives State from *;
   --
   --Step a BIT process along for machine C<State>
   --

   --=item *
   --
   procedure Fail_Next(State : in out Machine);
   --# derives State from *;
   --
   --Cause machine C<State> to fail the next BIT
   --


   --=item *
   --
   procedure Change_State
     (Word  : in Bus.Word;
      State : in out Machine);
   --# derives State from *, Word;
   --
   --Cause machine C<State> to act on a piece of data C<Word> which
   --has been read off the bus as part of a BIT request
   --

   --=item *
   --
   procedure Reset(State : in out Machine);
   --# derives State from *;
   --
   --Reset the BIT state of machine C<State>
   --
   --=back
   --
   --=cut

private
   type Machine is record
      Current_Phase : IBIT.Phase;
      Ticks : SystemTypes.Unsigned16;
      Fail_BIT : Boolean;
      Ticks_To_Complete : Systemtypes.Unsigned16;
   end record;

   Initial_Machine : constant Machine
     := Machine'(Current_Phase => Ibit.Off,
                 Ticks => 0,
                 Fail_Bit => False,
                 Ticks_To_Complete => 10);
end BIT_Machine;


--=head1 NOTES
--
--This package provides the abstract data type (ADT)
--C<BIT_Machine.Machine>, allowing subsystems to instantiate
--standard BIT machines as part of their internal state.
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
