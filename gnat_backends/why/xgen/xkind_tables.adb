------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         X K I N D _ T A B L E S                          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute it and/or modify it   --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Utils; use Utils;

package body Xkind_Tables is

   ---------------------
   -- Base_Id_Subtype --
   ---------------------

   function Base_Id_Subtype
     (Prefix       : Wide_String;
      Kind         : Id_Kind;
      Multiplicity : Id_Multiplicity)
     return Wide_String
   is
   begin
      case Kind is
         when Opaque =>
            case Multiplicity is
               when Id_One | Id_Lone =>
                  return "Why_Node_Id";
               when Id_Some | Id_Set =>
                  return "Why_Node_List";
            end case;
         when Unchecked =>
            return Id_Subtype (Prefix, Opaque, Multiplicity);
          when Regular =>
            return Id_Subtype (Prefix, Unchecked, Multiplicity);
      end case;
   end Base_Id_Subtype;

   -----------------
   -- Cache_Check --
   -----------------

   function Cache_Check
     (Prefix : Wide_String;
      M      : Id_Multiplicity)
     return Wide_String
   is
   begin
      return Strip_Prefix (Prefix)
        & Multiplicity_Suffix (M)
        & "_Cache_Valid";
   end Cache_Check;

   --------------------
   -- Children_Check --
   --------------------

   function Children_Check
     (Prefix : Wide_String;
      M      : Id_Multiplicity)
     return Wide_String is
   begin
      return Strip_Prefix (Prefix)
        & Multiplicity_Suffix (M)
        & "_Children_Valid";
   end Children_Check;

   -----------------
   -- Class_First --
   -----------------

   function Class_First (CI : Class_Info) return Why_Node_Kind is
   begin
      return Why_Node_Kind'Wide_Value (CI.First.all);
   end Class_First;

   ----------------
   -- Class_Last --
   ----------------

   function Class_Last (CI : Class_Info) return Why_Node_Kind is
   begin
      return Why_Node_Kind'Wide_Value (CI.Last.all);
   end Class_Last;

   ----------------
   -- Class_Name --
   ----------------

   function Class_Name (CI : Class_Info) return Wide_String is
   begin
      return CI.Name.all;
   end Class_Name;

   ----------------
   -- Id_Subtype --
   ----------------

   function Id_Subtype
     (Prefix       : Wide_String;
      Kind         : Id_Kind;
      Multiplicity : Id_Multiplicity)
     return Wide_String
   is
      function Kind_Suffix return Wide_String;
      --  Return the kind-specific part of the suffix

      -----------------
      -- Kind_Suffix --
      -----------------

      function Kind_Suffix return Wide_String is
      begin
         case Kind is
            when Opaque =>
               return "_Opaque";
            when Unchecked =>
               return "_Unchecked";
            when Regular =>
               return "";
         end case;
      end Kind_Suffix;

   begin
      return Prefix & Kind_Suffix & Multiplicity_Suffix (Multiplicity);
   end Id_Subtype;

   ----------------
   -- Kind_Check --
   ----------------

   function Kind_Check
     (Prefix : Wide_String;
      M      : Id_Multiplicity)
     return Wide_String is
   begin
      return Strip_Prefix (Prefix)
        & Multiplicity_Suffix (M)
        & "_Kind_Valid";
   end Kind_Check;

   -------------------------
   -- Multiplicity_Suffix --
   -------------------------

   function Multiplicity_Suffix
     (Multiplicity : Id_Multiplicity)
     return Wide_String is
   begin
      case Multiplicity is
         when Id_One =>
            return "_Id";
         when Id_Lone =>
            return "_OId";
         when Id_Some =>
            return "_List";
         when Id_Set =>
            return "_OList";
      end case;
   end Multiplicity_Suffix;

   ----------------
   -- Tree_Check --
   ----------------

   function Tree_Check
     (Prefix : Wide_String;
      M      : Id_Multiplicity)
     return Wide_String is
   begin
      return Strip_Prefix (Prefix)
        & Multiplicity_Suffix (M)
        & "_Valid";
   end Tree_Check;

end XKind_Tables;
