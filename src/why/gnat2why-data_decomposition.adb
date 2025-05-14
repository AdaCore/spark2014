------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--          G N A T 2 W H Y - D A T A _ D E C O M P O S I T I O N           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2023-2025, AdaCore                     --
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

with Ada.Containers.Indefinite_Hashed_Maps;
with Ada.Directories;
with Ada.Strings.Hash;
with Ada.Text_IO;
with Call;                       use Call;
with GNAT.OS_Lib;
with GNATCOLL.JSON;              use GNATCOLL.JSON;
with Lib;                        use Lib;
with Namet;                      use Namet;
with SPARK_Atree;                use SPARK_Atree;
with SPARK_Atree.Entities;       use SPARK_Atree.Entities;
with SPARK_Util;                 use SPARK_Util;
with String_Utils;               use String_Utils;
with VC_Kinds;                   use VC_Kinds;

package body Gnat2Why.Data_Decomposition is

   type Data_Decomposition_Entry is record
      Size        : Uint := No_Uint;
      Value_Size  : Uint := No_Uint;
      Object_Size : Uint := No_Uint;
      Alignment   : Uint := No_Uint;
   end record;

   package String_To_Data_Decomposition_Maps is new
     Ada.Containers.Indefinite_Hashed_Maps
       (Key_Type        => String,
        Element_Type    => Data_Decomposition_Entry,
        Hash            => Ada.Strings.Hash,
        Equivalent_Keys => "=",
        "="             => "=");

   Data_Decomposition_Table : String_To_Data_Decomposition_Maps.Map;

   -------------------------
   -- Get_Attribute_Value --
   -------------------------

   function Get_Attribute_Value
     (E       : Entity_Id;
      Attr_Id : Repr_Attribute_Id) return Uint
   is
      Data_Entry : Data_Decomposition_Entry;
   begin
      --  Return the known value if any
      case Attr_Id is
         when Attribute_Alignment =>
            if Known_Alignment (E) then
               return Alignment (E);
            end if;

         when Attribute_Size =>
            if Is_Type (E) then
               if Known_RM_Size (E) then
                  return RM_Size (E);
               end if;
            else
               pragma Assert (Is_Object (E));
               if Known_Esize (E) then
                  return Esize (E);
               end if;
            end if;

         when Attribute_Value_Size =>
            pragma Assert (Is_Type (E));
            if Known_RM_Size (E) then
               return RM_Size (E);
            end if;

         when Attribute_Object_Size =>
            pragma Assert (Is_Type (E));
            if Known_Esize (E) then
               return Esize (E);
            end if;

         when Attribute_Component_Size =>
            if Known_Component_Size (E) then
               return Component_Size (E);
            end if;
      end case;

      --  Otherwise check if data representation contains it
      declare
         Loc : constant String :=
           Location_String (Sloc (E), Mode => Data_Decomposition_Mode);
      begin
         if Data_Decomposition_Table.Contains (Loc) then
            Data_Entry :=
              Data_Decomposition_Table.Element (Loc);
         end if;
      end;

      if Attr_Id = Attribute_Alignment then
         return Data_Entry.Alignment;

      elsif Is_Type (E) then

         --  If value of Size is present for a type, it means that Esize
         --  (storing the value of Object_Size) and RM_Size (storing
         --  the value of Value_Size) for the type are equal. See
         --  Repinfo.List_Common_Type_Info

         if Present (Data_Entry.Size) then
            return Data_Entry.Size;
         else
            case Size_Attribute_Id'(Attr_Id) is
               when Attribute_Size
                  | Attribute_Value_Size
               =>
                  return Data_Entry.Value_Size;

               when Attribute_Object_Size =>
                  return Data_Entry.Object_Size;
               when Attribute_Component_Size =>
                  return No_Uint;
            end case;
         end if;

      --  Only attribute Size applies to an object. It is either the specified
      --  value of Size for the object, or the same as Typ'Object_Size for the
      --  type of the object.

      else
         pragma Assert (Is_Object (E));
         pragma Assert (Attr_Id = Attribute_Size);

         if Present (Data_Entry.Size) then
            return Data_Entry.Size;
         else
            return Get_Attribute_Value (Etype (E), Attribute_Object_Size);
         end if;
      end if;
   end Get_Attribute_Value;

   ---------------------------------------
   -- Read_Data_Decomposition_JSON_File --
   ---------------------------------------

   procedure Read_Data_Decomposition_JSON_File is

      procedure Handle_Entry (JSON_Entry : JSON_Value);
      --  Insert an entry in the map Data_Decomposition_Table

      function Handle_Field
        (JSON_Entry : JSON_Value; Field : String) return Uint;
      --  Return the optional data decomposition entry corresponding to Field
      --  in JSON_Entry, when possible.

      ------------------
      -- Handle_Entry --
      ------------------

      procedure Handle_Entry (JSON_Entry : JSON_Value) is
         Location   : constant String := Get (JSON_Entry, "location");
         Data_Entry : Data_Decomposition_Entry;
      begin
         Data_Entry.Size        := Handle_Field (JSON_Entry, "Size");
         Data_Entry.Value_Size  := Handle_Field (JSON_Entry, "Value_Size");
         Data_Entry.Object_Size := Handle_Field (JSON_Entry, "Object_Size");
         Data_Entry.Alignment   := Handle_Field (JSON_Entry, "Alignment");

         --  Subunits ("separates") may lead to duplicate entries for the same
         --  type or object, in files for the subunit and the main unit.
         if Data_Decomposition_Table.Contains (Location)
           and then Data_Entry /= Data_Decomposition_Table.Element (Location)
         then
            raise Program_Error
              with "inconsistent data representation duplicate";
         end if;

         Data_Decomposition_Table.Include (Location, Data_Entry);
      end Handle_Entry;

      ------------------
      -- Handle_Field --
      ------------------

      function Handle_Field
        (JSON_Entry : JSON_Value; Field : String) return Uint
      is
         function To_UI is new UI_From_Integral (Long_Long_Integer);
      begin
         --  We must check whether each value is of integer type, as the value
         --  "??" is used in -gnatR2 mode to indicate that the numerical value
         --  depends on back annotations by gigi, for variants of records whose
         --  size depends on discriminants or other values. See comments in
         --  repinfo.ads for details.

         if Has_Field (JSON_Entry, Field)
           and then Kind (Get (JSON_Entry, Field)) = JSON_Int_Type
         then
            return To_UI (Get (Get (JSON_Entry, Field)));
         else
            return No_Uint;
         end if;
      end Handle_Field;

      --  Local variables

      File_Names : String_Sets.Set;

   --  Start of processing for Read_Data_Decomposition_JSON_File

   begin
      for J in Main_Unit .. Last_Unit loop

         --  Ignore units with no compilation unit. Those are pragma
         --  configuration units and they have no data decomposition.

         if Present (Cunit (J)) then
            declare
               Source_File_Name : constant String :=
                 Get_Name_String (Unit_File_Name (J));
               JSON_File_Name : constant String :=
                 Ada.Directories.Compose
                   (Containing_Directory => Data_Representation_Subdir_Name,
                    Name                 => Source_File_Name,
                    Extension            => "json");
            begin
               if not File_Names.Contains (Source_File_Name)
                 and then Ada.Directories.Exists (JSON_File_Name)
               then
                  declare
                     File    : constant JSON_Value :=
                       Read_File_Into_JSON (JSON_File_Name);
                     Entries : constant JSON_Array := Get (File);
                  begin
                     for Index in 1 .. Length (Entries) loop
                        Handle_Entry (Get (Entries, Index));
                     end loop;

                     File_Names.Insert (Source_File_Name);
                  end;
               end if;
            exception
               when others =>
                  pragma Annotate
                    (Xcov, Exempt_On, "only triggered by older buggy GNAT");
                  Ada.Text_IO.Put_Line
                    (Ada.Text_IO.Standard_Error,
                     "error: GNAT generated an ill-formed JSON file "
                     & JSON_File_Name
                     & " for data representation.");
                  Ada.Text_IO.Put_Line
                    (Ada.Text_IO.Standard_Error,
                     "error: Try installing a more recent version of GNAT.");
                  Ada.Text_IO.Put_Line
                    (Ada.Text_IO.Standard_Error,
                     "error: As possible workarounds, remove GNAT from your "
                     & "PATH or use the switch -gnateT=<target.atp> to pass "
                     & "an explicit target parametrization file.");
                  GNAT.OS_Lib.OS_Exit (1);
                  pragma Annotate (Xcov, Exempt_Off);
            end;
         end if;
      end loop;
   end Read_Data_Decomposition_JSON_File;

end Gnat2Why.Data_Decomposition;
