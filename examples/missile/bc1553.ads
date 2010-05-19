--=head1 NAME
--
-- bc1553 - the 1553 bus interface for the Bus Controller (BC)
--
--=head1 REVISION HISTORY
--
-- $Log: bc1553.ads,v $
-- Revision 1.2  2004/12/19 15:53:40  adi
-- Added POD to airspeed, barometer, bc1553
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.7  2003/08/17 22:06:24  adi
-- Added lru_number
--
-- Revision 1.6  2003/02/12 21:22:45  adi
-- Added Set_Message-Valid
--
-- Revision 1.5  2003/02/11 20:14:21  adi
-- Added fresh and valid checking functions
--
-- Revision 1.4  2003/02/05 22:49:00  adi
-- Fixed for renamed types
--
-- Revision 1.3  2003/02/03 23:17:17  adi
-- Added Acknowledge_Message
--
-- Revision 1.2  2003/02/03 18:26:27  adi
-- Moved the interesting stuff into bus.ads
--
-- Revision 1.1  2002/10/27 20:40:21  adi
-- Initial revision
--
--=cut
with Bus;
with SystemTypes;
--# inherit SystemTypes,Bus;
package BC1553
is
   --=head1 TYPES
   --
   --=over 4
   --
   --=cut

   --=item *
   --
   type Lru_Name is
     (Barometer,
      Asi,
      Ins,
      Compass,
      Fuel,
      Fuze,
      Radar,
      Infrared,
      Fins,
      Motor,
      Destruct,
      Warhead
     );
   --
   --Symbolic names for the Lrus
   --
   --=cut

   --=back
   --
   --=head1 SUBPROGRAMS
   --
   --=over 4

   --=item *
   --
   function Lru_Number(L : Lru_Name) return Bus.Lru_Index;
   --
   --Map LRU name C<L> to the number of the LRU on the bus
   --

   --=item *
   --
   procedure Set_Message_Valid(Subaddress_Idx : in Bus.Lru_Subaddress_Index;
                               Dest    : in Lru_Name);
   --# global in out Bus.Outputs;
   --# derives Bus.Outputs from *, Subaddress_Idx, Dest;
   --
   --Write out data from subaddress C<Subaddress_Idx> from
   --the BC to the RT called C<Dest>.
   --

   --=item *
   --
   procedure Write_Word
     (Data           : in Bus.Word;
      Idx            : in Bus.Word_Index;
      Subaddress_Idx : in Bus.Lru_Subaddress_Index;
      Dest           : in Lru_Name);
   --# global in out Bus.Outputs;
   --# derives Bus.Outputs from *, Data, Idx, Subaddress_Idx, Dest;
   --
   --Write a word of data C<Data> to index C<Idx> in subaddress
   --C<Subaddress_Idx>, destined for LRU C<Dest>.
   --

   --=item *
   --
   procedure Write_Message
     (Data           : in Bus.Message;
      Subaddress_Idx : in Bus.Lru_Subaddress_Index;
      Dest           : in Lru_Name);
   --# global in out Bus.Outputs;
   --# derives Bus.Outputs from *, Data, Subaddress_Idx, Dest;
   --
   --Write an entire message of data C<Data> at subaddress
   --C<Subaddress_Idx>, destined for LRU C<Dest>.
   --

   --=item *
   --
   function Is_Fresh
     (Src            : Lru_Name;
      Subaddress_Idx : Bus.Lru_Subaddress_Index)
     return Boolean;
   --# global in Bus.Inputs;
   --
   --See if a message from LRU C<Src> at subaddress
   --C<Subaddress_Idx> is fresh.
   --

   --=item *
   --
   function Is_Valid
     (Src : Lru_Name;
      Subaddress_Idx : Bus.Lru_Subaddress_Index)
     return Boolean;
   --# global in Bus.Inputs;
   --
   --See if a message from LRU C<Src> at subaddress
   --C<Subaddress_Idx> is valid.
   --

   --=item *
   --
   procedure Read_Word
     (Src            : in  Lru_Name;
      Idx            : in  Bus.Word_Index;
      Subaddress_Idx : in  Bus.Lru_Subaddress_Index;
      Data           : out Bus.Word);
   --# global in Bus.Inputs;
   --# derives Data from Src, Idx, Subaddress_Idx, Bus.Inputs;
   --
   --Read data word C<Data> sent to the BC from LRU C<Src> at
   --word C<Idx>, subaddress C<Subaddress_Idx>.
   --

   --=item *
   --
   procedure Read_Message
     (Src            : in  Lru_Name;
      Subaddress_Idx : in  Bus.Lru_Subaddress_Index;
      Data           : out Bus.Message);
   --# global in Bus.Inputs;
   --# derives Data from Src, Subaddress_Idx, Bus.Inputs;
   --
   --Read message data C<Data> from LRU C<Src> at
   --subaddress C<Subaddress_Idx>.
   --

   --=item *
   --
   procedure Acknowledge_Message
     (Src            : in  Lru_Name;
      Subaddress_Idx : in  Bus.Lru_Subaddress_Index);
   --# global in out Bus.Inputs;
   --# derives Bus.Inputs from *, Src, Subaddress_Idx;
   --
   --Acknowledge a message from LRU C<Src> from subaddress
   --C<Subaddress_Idx> as fresh.
   --

   --=back
   --
   --=cut
end BC1553;

--=head1 NOTES
--
--All other system components are on the bus as remote
--terminals (RTs). R messages go BC -> RT.  T messages go RT -> BC
--
--This package provides a simulator of a 1553 Bus Controller.
--It allows the main system (the BC) to communicate data to the
--interfacing LRUs (the RTs).
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

