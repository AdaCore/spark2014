------------------------------------------------------------------------------
--                                                                          --
--                           GNATPROVE COMPONENTS                           --
--                                                                          --
--                             H A S H _ C O N S                            --
--                                                                          --
--                                  S p e c                                 --
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

with Ada.Containers;

generic
   type Elt_Type is private;
   type Access_Type is not null access constant Elt_Type;
   with function Hash (E : Elt_Type) return Ada.Containers.Hash_Type;
   with function "=" (E1, E2 : Elt_Type) return Boolean;
package Hash_Cons is

   function Hash_Cons (E : Elt_Type) return Access_Type;

   function Hash (A : Access_Type) return Ada.Containers.Hash_Type;

end Hash_Cons;
