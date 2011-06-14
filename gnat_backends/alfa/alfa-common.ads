------------------------------------------------------------------------------
--                                                                          --
--                         GNAT BACK-END COMPONENTS                         --
--                                                                          --
--                           A L F A . C O M M O N                          --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--             Copyright (C) 2011, Free Software Foundation, Inc.           --
--                                                                          --
-- GNAT is free software;  you can  redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License --
-- for  more details.  You should have  received  a copy of the GNU General --
-- Public License  distributed with GNAT; see file COPYING3.  If not, go to --
-- http://www.gnu.org/licenses for a complete copy of the license.          --
--                                                                          --
-- GNAT was originally developed  by the GNAT team at  New York University. --
-- Extensive contributions were provided by Ada Core Technologies Inc.      --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers;             use Ada.Containers;
with Ada.Containers.Hashed_Sets;
with Ada.Strings.Hash;
with Ada.Strings.Unbounded;      use Ada.Strings.Unbounded;

with AA_Util;               use AA_Util;
with Atree; use Atree;
with Einfo; use Einfo;
with Namet; use Namet;
with Sinfo; use Sinfo;
with Sinput; use Sinput;

package Alfa.Common is

   Name_GNATprove : constant String := "gnatprove";

   function Id_Hash (X : Entity_Id) return Hash_Type is (Hash_Type (X));

   package Id_Set is new Hashed_Sets
     (Element_Type        => Entity_Id,
      Hash                => Id_Hash,
      Equivalent_Elements => "=",
      "="                 => "=");
   use Id_Set;

   function UString_Hash (X : Unbounded_String) return Hash_Type is
     (Ada.Strings.Hash (To_String (X)));

   package UString_Set is new Hashed_Sets
     (Element_Type        => Unbounded_String,
      Hash                => UString_Hash,
      Equivalent_Elements => "=",
      "="                 => "=");
   use UString_Set;

   function Is_Package_Level_Entity (E : Entity_Id) return Boolean is
     (Ekind (Scope (E)) = E_Package);

   function File_Name_Without_Suffix (Loc : Source_Ptr) return String is
      (File_Name_Without_Suffix
         (Get_Name_String (File_Name (Get_Source_File_Index (Loc)))));

end Alfa.Common;
