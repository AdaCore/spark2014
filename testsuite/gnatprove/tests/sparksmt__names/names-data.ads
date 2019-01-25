------------------------------------------------------------------------------
--                                                                          --
--                           SPARKSMT COMPONENTS                            --
--                                                                          --
--                           N A M E S . D A T A                            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--               Copyright (C) 2016, Altran UK Limited                      --
--                                                                          --
-- sparksmt is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  sparksmt is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  sparksmt;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers;                use Ada.Containers;
with Ada.Containers.Formal_Indefinite_Vectors;

private package Names.Data with
   SPARK_Mode
is

   -------------
   -- General --
   -------------

   subtype Valid_Name_Id is Name_Id range 1 .. Name_Id'Last;

   ------------------
   -- Hash_Table_T --
   ------------------

   Hash_Table_Size : constant := 256;
   subtype Hash_Table_Index_T is Hash_Type range 0 .. (Hash_Table_Size - 1);
   type Hash_Table_T is array (Hash_Table_Index_T) of Name_Id;

   -----------------
   -- Char_Tables --
   -----------------

   type Char_Table_Index is range 0 .. 2 ** 31 - 2;

   function Eq (A, B : Character) return Boolean is (A = B);
   --  Workaround for P414-029

   package Char_Tables is new Ada.Containers.Formal_Indefinite_Vectors
     (Index_Type   => Char_Table_Index,
      Element_Type => Character,
      Bounded      => False,
      Max_Size_In_Storage_Elements => Character'Size);

   ------------------
   -- Entry_Tables --
   ------------------

   type Name_Entry is record
      Table_Index : Char_Table_Index;
      Length      : Positive;
      Next_Hash   : Name_Id;
   end record
     with Size => 96;

   function Eq (A, B : Name_Entry) return Boolean is (A = B);
   --  Workaround for P414-029

   package Entry_Tables is new Ada.Containers.Formal_Indefinite_Vectors
     (Index_Type   => Valid_Name_Id,
      Element_Type => Name_Entry,
      Bounded      => False,
      Max_Size_In_Storage_Elements => Name_Entry'Size);

end Names.Data;
