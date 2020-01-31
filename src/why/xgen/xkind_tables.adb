------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         X K I N D _ T A B L E S                          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Characters.Conversions; use Ada.Characters.Conversions;
with GNAT.Case_Util;             use GNAT.Case_Util;
with Utils;                      use Utils;
with Xtree_Tables;               use Xtree_Tables;
with Ada.Wide_Text_IO;           use Ada.Wide_Text_IO;

package body Xkind_Tables is

   --------------
   -- Arr_Type --
   --------------

   function Arr_Type
     (Prefix : Wide_String;
      Kind   : Id_Kind)
     return Wide_String is
   begin
      if Kind = Derived then
         return Prefix & "_Array";
      else
         return Prefix & "_V_Array";
      end if;
   end Arr_Type;

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
         when Derived =>
            return Id_Subtype (Prefix, Regular, Multiplicity);
      end case;
   end Base_Id_Subtype;

   -----------------
   -- Cache_Check --
   -----------------

   function Cache_Check (M : Id_Multiplicity) return Wide_String
   is
   begin
      return Strip_Prefix (Multiplicity_Suffix (M)) & "_Cache_Valid";
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

   ------------------
   -- Default_Kind --
   ------------------

   function Default_Kind return Why_Node_Kind is
   begin
      return Why_Node_Kind'First;
   end Default_Kind;

   function Default_Kind return Wide_String is
   begin
      return Mixed_Case_Name (Default_Kind);
   end Default_Kind;

   ---------------------
   -- Display_Domains --
   ---------------------

   procedure Display_Domains is
   begin
      for Kind in Valid_Kind'Range loop
         Put_Line (Mixed_Case_Name (Kind) & " : "
                   & EW_ODomain'Wide_Image (Get_Domain (Kind)));
      end loop;
   end Display_Domains;

   ----------------
   -- Get_Domain --
   ----------------

   function Get_Domain (Id_Type : Wide_String) return EW_ODomain is
      Prefix : constant Wide_String := Strip_Suffix (Id_Type);
      Kind   : constant Wide_String := Suffix (Prefix);
      Last   : Natural := Prefix'Last;
   begin
      if Kind = "Unchecked"
        or else Kind = "Valid"
        or else Kind = "Opaque"
      then
         Last := Last - (Kind'Length + 1);
      end if;

      for CI of Classes loop
         if Is_Domain (CI) then
            declare
               Prefix : constant Wide_String := Class_Name (CI) & "_";
            begin
               if Prefix =
                 Id_Type (Id_Type'First .. Id_Type'First + Prefix'Length - 1)
               then
                  return EW_ODomain'Wide_Value ("E" & Class_Name (CI));
               end if;
            end;
         end if;
      end loop;

      --  Fallback on the most general domain: W_Expr

      return Get_Domain ("W_Expr_Id");
   end Get_Domain;

   --------------------
   -- Freeze_Domains --
   --------------------

   procedure Init_Domains is
      Domain_Ambiguity : array (Why_Node_Kind) of Boolean := (others => False);
   begin
      for CI of Classes loop
         if Is_Domain (CI) then
            declare
               DK : constant EW_ODomain :=
                      EW_ODomain'Wide_Value ("E" & Class_Name (CI));
            begin
               for Kind in Class_First (CI) .. Class_Last (CI) loop
                  if Domain_Ambiguity (Kind) then
                     null;

                  elsif Is_Subclass (CI, Get_Domain (Kind)) then
                     Set_Domain (Kind, DK);

                  elsif Is_Subclass (Get_Domain (Kind), CI)
                    or else Get_Domain (Kind) = CI
                  then
                     null;

                  else
                     Set_Domain (Kind, EW_Expr);
                     Domain_Ambiguity (Kind) := True;
                  end if;
               end loop;
            end;
         end if;
      end loop;
   end Init_Domains;

   ----------------
   -- Id_Subtype --
   ----------------

   function Id_Subtype
     (N_Kind       : Why_Node_Kind;
      I_Kind       : Id_Kind := Regular;
      Multiplicity : Id_Multiplicity := Id_One)
     return Wide_String is
   begin
      return Id_Subtype (Mixed_Case_Name (N_Kind), I_Kind, Multiplicity);
   end Id_Subtype;

   function Id_Subtype
     (Prefix       : Wide_String;
      Kind         : Id_Kind := Regular;
      Multiplicity : Id_Multiplicity := Id_One)
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
               return "_Valid";
            when Derived =>
               return "";
         end case;
      end Kind_Suffix;

   begin
      return Prefix
        & Kind_Suffix
        & Multiplicity_Suffix (Multiplicity);
   end Id_Subtype;

   ---------------
   -- Is_Domain --
   ---------------

   function Is_Domain (CI : Class_Info) return Boolean is
   begin
      return CI.Father /= null;
   end Is_Domain;

   function Is_Domain (Id_Type : Wide_String) return Boolean is
   begin
      return Get_Domain (Id_Type) /= EW_Expr;
   end Is_Domain;

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

   ---------------------
   -- Mixed_Case_Name --
   ---------------------

   function Mixed_Case_Name (Kind : Why_Node_Kind) return Wide_String is
      Name : String := Why_Node_Kind'Image (Kind);
   begin
      To_Mixed (Name);
      return To_Wide_String (Name);
   end Mixed_Case_Name;

   function Mixed_Case_Name (M : Id_Multiplicity) return Wide_String is
      Name : String := Id_Multiplicity'Image (M);
   begin
      To_Mixed (Name);
      return To_Wide_String (Name);
   end Mixed_Case_Name;

   function Mixed_Case_Name (D : EW_ODomain) return Wide_String is
      Name : String := EW_ODomain'Image (D);
   begin
      To_Mixed (Name (2 .. Name'Last));
      return To_Wide_String (Name);
   end Mixed_Case_Name;

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

   ---------------
   -- New_Class --
   ---------------

   procedure New_Class
     (Name  : Wide_String;
      First : Why_Node_Kind;
      Last  : Why_Node_Kind)
   is
      CI : constant Class_Info :=
             (Name   => new Wide_String'(Name),
              Father => null,
              First  => new Wide_String'(Mixed_Case_Name (First)),
              Last   => new Wide_String'(Mixed_Case_Name (Last)));
   begin
      Classes.Append (CI);
   end New_Class;

   ----------------
   -- New_Domain --
   ----------------

   procedure New_Domain
     (Name   : Wide_String;
      Father : Wide_String;
      First  : Why_Node_Kind;
      Last   : Why_Node_Kind)
   is
      CI : constant Class_Info :=
             (Name   => new Wide_String'(Name),
              Father => new Wide_String'(Father),
              First  => new Wide_String'(Mixed_Case_Name (First)),
              Last   => new Wide_String'(Mixed_Case_Name (Last)));
   begin
      Classes.Append (CI);
   end New_Domain;

   ------------------
   -- Is_Subdomain --
   ------------------

   function Is_Subclass (Inner, Outer : Class_Info) return Boolean is
      FI : constant Why_Node_Kind := Class_First (Inner);
      LI : constant Why_Node_Kind := Class_Last (Inner);
      FO : constant Why_Node_Kind := Class_First (Outer);
      LO : constant Why_Node_Kind := Class_Last (Outer);
   begin

      --  When the bounds are equal, Inner is a strict subclass of Outer iff
      --  Outer is not a domain and Inner is; indeed a domain class has the
      --  constraint that any node of this class must have the corresponding
      --  domain, whereas a regular class does not have this constraint and is
      --  therefore more general (i.e. accepts more nodes).
      --  The idea is to have the most complete ordering possible; when we
      --  cannot order using bounds, we still have a sensible way to order
      --  using domains.

      if LI = LO and then FI = FO then
         return Is_Domain (Inner) and then not Is_Domain (Outer);

      --  Otherwise, when bounds are different, just check that
      --  Inner.First .. Inner.Last is a strict subrange of
      --  Outer.First .. Outer.Last *without considering the domain*:
      --  still with the idea to have the most complete ordering possible,
      --  so avoiding constraints that would make some classes incomparable.

      else
         return FI in  FO .. LO and then LI in FO .. LO;
      end if;
   end Is_Subclass;

   --------------------
   -- Register_Kinds --
   --------------------

   procedure Register_Kinds is
   begin
      for Kind in Why_Node_Kind'Range loop
         Kinds.Append (new Wide_String'(Mixed_Case_Name (Kind)));
      end loop;
   end Register_Kinds;

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

end Xkind_Tables;
