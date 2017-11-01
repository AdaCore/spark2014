------------------------------------------------------------------------------
--                                                                          --
--                           GNATPROVE COMPONENTS                           --
--                                                                          --
--                             H A S H _ C O N S                            --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                     Copyright (C) 2010-2017, AdaCore                     --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers.Hashed_Maps;
with System.Storage_Elements;

package body Hash_Cons is

   package Cons_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Elt_Type,
        Element_Type    => Access_Type,
        Hash            => Hash,
        Equivalent_Keys => "=",
        "="             => "=");

   Cons_Table : Cons_Maps.Map := Cons_Maps.Empty_Map;

   ----------
   -- Hash --
   ----------

   function Hash (A : Access_Type) return Ada.Containers.Hash_Type is
      use Ada.Containers;
      use System.Storage_Elements;

      Addr : constant Integer_Address :=
        To_Integer (A.all'Address) mod 2147483647;
      --  ??? why 2147483647?
   begin
      return Hash_Type (Addr);
   end Hash;

   ---------------
   -- Hash_Cons --
   ---------------

   function Hash_Cons (E : Elt_Type) return Access_Type is
      use Cons_Maps;
      C : constant Cursor := Cons_Table.Find (E);
   begin
      if Has_Element (C) then
         return Element (C);
      else
         declare
            N_Ptr : constant Access_Type := new Elt_Type'(E);
         begin
            Cons_Table.Insert (E, N_Ptr);
            return N_Ptr;
         end;
      end if;
   end Hash_Cons;

end Hash_Cons;
