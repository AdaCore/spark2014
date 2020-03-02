------------------------------------------------------------------------------
--                                                                          --
--                           GNATPROVE COMPONENTS                           --
--                                                                          --
--                             H A S H _ C O N S                            --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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

with Ada.Containers.Hashed_Sets;

package body Hash_Cons is

   function Equivalent_Elements (Left, Right : Access_Type) return Boolean;

   package Cons_Sets is new
     Ada.Containers.Hashed_Sets
       (Element_Type        => Access_Type,
        Hash                => Hash,
        Equivalent_Elements => Equivalent_Elements,
        "="                 => "=");

   Cons_Table : Cons_Sets.Set := Cons_Sets.Empty_Set;

   -------------------------
   -- Equivalent_Elements --
   -------------------------

   function Equivalent_Elements (Left, Right : Access_Type) return Boolean is
   begin
      return Left.all = Right.all;
   end Equivalent_Elements;

   ----------
   -- Hash --
   ----------

   function Hash (A : Access_Type) return Ada.Containers.Hash_Type is
   begin
      return Hash (A.all);
   end Hash;

   ---------------
   -- Hash_Cons --
   ---------------

   function Hash_Cons (E : Elt_Type) return Access_Type is
      use Cons_Sets;
      C : constant Cursor := Cons_Table.Find (E'Unrestricted_Access);
   begin
      if Has_Element (C) then
         return Element (C);
      else
         declare
            N_Ptr : constant Access_Type := new Elt_Type'(E);
         begin
            Cons_Table.Insert (N_Ptr);
            return N_Ptr;
         end;
      end if;
   end Hash_Cons;

end Hash_Cons;
