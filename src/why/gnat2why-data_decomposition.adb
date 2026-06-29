------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--          G N A T 2 W H Y - D A T A _ D E C O M P O S I T I O N           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2023-2026, AdaCore                     --
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
with Ada.Exceptions;
with Ada.Strings.Hash;
with Ada.Text_IO;
with GNAT.OS_Lib;
with GNATCOLL.JSON;        use GNATCOLL.JSON;
with GNATCOLL.Buffer;
with GNATCOLL.String_Builders;
with Lib;                  use Lib;
with Namet;                use Namet;
with SPARK_Atree;          use SPARK_Atree;
with SPARK_Atree.Entities; use SPARK_Atree.Entities;
with SPARK_Util;           use SPARK_Util;
with String_Utils;         use String_Utils;

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

   procedure Add_Entry
     (Name, Location : String; Data_Entry : Data_Decomposition_Entry)
   with Pre => Name'Length > 0 and then Location'Length > 0;
   --  Add entry with data decomposition

   ---------------
   -- Add_Entry --
   ---------------

   procedure Add_Entry
     (Name, Location : String; Data_Entry : Data_Decomposition_Entry)
   is
      pragma Unreferenced (Name);
      Inserted : Boolean;
      Position : String_To_Data_Decomposition_Maps.Cursor;
   begin
      Data_Decomposition_Table.Insert
        (Location, Data_Entry, Position, Inserted);

      --  Subunits ("separates") may lead to duplicate entries for the same
      --  type or object, in files for the subunit and the main unit.
      if not Inserted
        and then Data_Entry /= Data_Decomposition_Table (Position)
      then
         raise Program_Error with "inconsistent data representation duplicate";
      end if;
   end Add_Entry;

   -------------------------
   -- Get_Attribute_Value --
   -------------------------

   function Get_Attribute_Value
     (E : Entity_Id; Attr_Id : Repr_Attribute_Id) return Uint
   is
      Data_Entry : Data_Decomposition_Entry;
   begin
      --  Return the known value if any
      case Attr_Id is
         when Attribute_Alignment      =>
            if Known_Alignment (E) then
               return Alignment (E);
            end if;

         when Attribute_Size           =>
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

         when Attribute_Value_Size     =>
            pragma Assert (Is_Type (E));
            if Known_RM_Size (E) then
               return RM_Size (E);
            end if;

         when Attribute_Object_Size    =>
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
            Data_Entry := Data_Decomposition_Table.Element (Loc);
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
               when Attribute_Size | Attribute_Value_Size =>
                  return Data_Entry.Value_Size;

               when Attribute_Object_Size                 =>
                  return Data_Entry.Object_Size;

               when Attribute_Component_Size              =>
                  return No_Uint;
            end case;
         end if;

      --  Only attribute Size applies to an object

      else
         pragma Assert (Is_Object (E));
         pragma Assert (Attr_Id = Attribute_Size);

         return Data_Entry.Size;
      end if;
   end Get_Attribute_Value;

   procedure Read_JSON (File : String);
   --  Read data representation file using a custom parser that supports
   --  universal integers to handle object sizes that exceed the range of
   --  native integer types supported by GNATCOLL.JSON.

   ---------------
   -- Read_JSON --
   ---------------

   procedure Read_JSON (File : String) is
      Data : GNATCOLL.Buffer.Reader'Class := GNATCOLL.Buffer.Open (File);
      --  ??? We make this a class-wide object to workaround an obscure problem
      --  with built-in-place function calls from GNATprove (which is built
      --  with No_Tasking restriction) to GNATCOLL (which is built with no
      --  restrictions).

      Parser : JSON_Parser;
      Event  : JSON_Parser_Event;
      --  Global objects accessed by both parsing and error reporting routines

      use GNATCOLL.String_Builders;

      procedure Bad_Input
      with No_Return;
      --  Report bad file input, e.g. ill-formed or unexpected JSON data

      --  The following routines handle individial JSON elements. The valid
      --  input data looks like:
      --   [
      --     {"name": "foo_type",
      --      "location: "foo.ads:3:3",
      --      "Size": 8},
      --     {"name": "bar_type",
      --      "location: "foo.ads:6:3",
      --      "Alignment": 8,
      --      "Small": 0.125}
      --   ]
      --  i.e. it is a JSON document with array of with objects with key-value
      --  pairs. Some of the unsupported keys might include objects or arrays
      --  that must be ignored (e.g. with complex representation for variants
      --  and discriminant-dependent components).

      function Current_Token return String;
      --  Return current token from the parser

      procedure Ignore;
      --  Ignore next input item; called for data representation info that we
      --  don't use.

      procedure Parse_Next_Event;
      --  Read next token in from the event-driven parser

      procedure Read_Doc
      with Post => Event.Kind = DOC_END;
      --  Main routine for reading the JSON document

      procedure Read_Type_Array
      with Pre => Event.Kind = ARRAY_START, Post => Event.Kind = ARRAY_END;
      --  Read array of type representation items

      procedure Read_Type_Object
      with Pre => Event.Kind = OBJECT_START, Post => Event.Kind = OBJECT_END;
      --  Read object with data representation of a single type

      procedure Read_Integer_Value (Value : in out Uint);
      procedure Read_String_Value (Value : in out String_Builder);
      --  Read values of a JSON mapping

      function Unquote (S : String) return String
      with
        Pre  =>
          S'Length >= 2 and then S (S'First) = '"' and then S (S'Last) = '"',
        Post => Unquote'Result'Length = S'Length - 2;
      --  Utility routine; removes quotes from its parameter

      function UI_From_String (S : String) return Valid_Uint
      with Pre => S'Length > 0 and then (for all C of S => C in '0' .. '9');
      --  Conversion routine to read universal integers

      ---------------
      -- Bad_Input --
      ---------------

      procedure Bad_Input is
         Line, Column : Integer;
      begin
         --  Raise exception with file:line:column attached

         Data.Current_Text_Position (Line, Column);

         declare
            Line_Number   : constant String := Line'Img;
            Column_Number : constant String := Column'Img;
            Location      : constant String :=
              Line_Number (Line_Number'First + 1 .. Line_Number'Last)
              & ':'
              & Column_Number (Column_Number'First + 1 .. Column_Number'Last);
         begin
            raise Invalid_JSON_Stream with File & ':' & Location;
         end;
      end Bad_Input;

      -------------------
      -- Current_Token --
      -------------------

      function Current_Token return String is
      begin
         return GNATCOLL.Buffer.Token (Data, Event.First, Event.Last);
      end Current_Token;

      ------------
      -- Ignore --
      ------------

      procedure Ignore is

         procedure Ignore_Array
         with Pre => Event.Kind = ARRAY_START, Post => Event.Kind = ARRAY_END;

         procedure Ignore_Object
         with
           Pre  => Event.Kind = OBJECT_START,
           Post => Event.Kind = OBJECT_END;
         --  Routines for ignoring composite data while keeping track of the
         --  input structure.

         ------------------
         -- Ignore_Array --
         ------------------

         procedure Ignore_Array is
         begin
            loop
               Parse_Next_Event;

               if Event.Kind = DOC_END then
                  Bad_Input;
               elsif Event.Kind = ARRAY_END then
                  exit;
               elsif Event.Kind = ARRAY_START then
                  Ignore_Array;
               elsif Event.Kind = OBJECT_START then
                  Ignore_Object;
               else
                  null;
               end if;
            end loop;
         end Ignore_Array;

         -------------------
         -- Ignore_Object --
         -------------------

         procedure Ignore_Object is
         begin
            loop
               Parse_Next_Event;

               if Event.Kind = DOC_END then
                  Bad_Input;
               elsif Event.Kind = OBJECT_END then
                  exit;
               elsif Event.Kind = ARRAY_START then
                  Ignore_Array;
               elsif Event.Kind = OBJECT_START then
                  Ignore_Object;
               else
                  null;
               end if;
            end loop;
         end Ignore_Object;

      begin
         Parse_Next_Event;

         case Event.Kind is
            when ARRAY_START                                 =>
               Ignore_Array;

            when OBJECT_START                                =>
               Ignore_Object;

            when INTEGER_VALUE | NUMBER_VALUE | STRING_VALUE =>
               null;

            when others                                      =>
               Bad_Input;
         end case;
      end Ignore;

      ----------------------
      -- Parse_Next_Event --
      ----------------------

      procedure Parse_Next_Event is
      begin
         Event := Parse_Next (Parser, GNATCOLL.Buffer.Reader (Data));
      exception
         when Invalid_JSON_Stream =>
            --  Propagate exception with location of the error attached
            Bad_Input;
      end Parse_Next_Event;

      ---------------------
      -- Read_Array_Type --
      ---------------------

      procedure Read_Type_Array is
      begin
         loop
            Parse_Next_Event;

            if Event.Kind = ARRAY_END then
               exit;
            elsif Event.Kind = OBJECT_START then
               Read_Type_Object;
            else
               Bad_Input;
            end if;
         end loop;
      end Read_Type_Array;

      ------------------------
      -- Read_Integer_Value --
      ------------------------

      procedure Read_Integer_Value (Value : in out Uint) is
      begin
         --  Detect duplicate keys

         if Present (Value) then
            Bad_Input;
         end if;

         Parse_Next_Event;

         if Event.Kind = INTEGER_VALUE then
            Value := UI_From_String (Current_Token);

         elsif Event.Kind = STRING_VALUE then

            --  Value "??" indicates that the numerical value depends on back
            --  annotations by gigi, for variants of records whose size depends
            --  on discriminants or other values. See comments in repinfo.ads
            --  for details.

            if Unquote (Current_Token) = "??" then
               pragma Assert (No (Value));
            else
               Bad_Input;
            end if;
         else
            Bad_Input;
         end if;
      end Read_Integer_Value;

      -----------------------
      -- Read_String_Value --
      -----------------------

      procedure Read_String_Value (Value : in out String_Builder) is
      begin
         --  Detect duplicate keys

         if Length (Value) > 0 then
            Bad_Input;
         end if;

         Parse_Next_Event;

         if Event.Kind = STRING_VALUE then
            Set (Value, Unquote (Current_Token));
         else
            Bad_Input;
         end if;
      end Read_String_Value;

      ----------------------
      -- Read_Type_Object --
      ----------------------

      procedure Read_Type_Object is
         Name, Location : String_Builder;
         Data_Entry     : Data_Decomposition_Entry;
         --  Data read field-by-field from the file before we store it in the
         --  final map.

         function Is_Parent_Variant (Key : String) return Boolean
         with Ghost;
         --  Returns True if Key is of the form "(parent_)*variant"

         procedure Read_Value (Key : String);
         --  Read value mapped to a given Key

         -----------------------
         -- Is_Parent_Variant --
         -----------------------

         function Is_Parent_Variant (Key : String) return Boolean is
         begin
            if Key'Length > 7 then
               return
                 Key (Key'First .. Key'First + 6) = "parent_"
                 and then Is_Parent_Variant (Key (Key'First + 7 .. Key'Last));
            else
               return Key = "variant";
            end if;
         end Is_Parent_Variant;

         ----------------
         -- Read_Value --
         ----------------

         procedure Read_Value (Key : String) is
         begin
            if Key = "name" then
               Read_String_Value (Name);
            elsif Key = "location" then
               Read_String_Value (Location);
            elsif Key = "Size" then
               Read_Integer_Value (Data_Entry.Size);
            elsif Key = "Value_Size" then
               Read_Integer_Value (Data_Entry.Value_Size);
            elsif Key = "Object_Size" then
               Read_Integer_Value (Data_Entry.Object_Size);
            elsif Key = "Alignment" then
               Read_Integer_Value (Data_Entry.Alignment);
            else
               --  In debug builds we check what data we get from GNAT;
               --  in production builds we will simply ignore this data.

               pragma
                 Assert
                   (Key
                    in "Bit_Order"
                     | "Component_Size"
                     | "Linker_Section"
                     | "Range"
                     | "Scalar_Storage_Order"
                     | "Small"
                     | "record"
                    or else Is_Parent_Variant (Key),
                    "unknown data representation item " & Key);
               Ignore;
            end if;
         end Read_Value;

      begin
         loop
            --  Read object keys and their values

            Parse_Next_Event;

            if Event.Kind = OBJECT_END then
               exit;
            elsif Event.Kind = STRING_VALUE then
               Read_Value (Key => Unquote (Current_Token));
            else
               Bad_Input;
            end if;
         end loop;

         --  For a valid input we will have both name and location

         if Length (Name) > 0 and then Length (Location) > 0 then
            Add_Entry (As_String (Name), As_String (Location), Data_Entry);
         else
            Bad_Input;
         end if;
      end Read_Type_Object;

      --------------
      -- Read_Doc --
      --------------

      procedure Read_Doc is
      begin
         Parse_Next_Event;

         --  Gently accept empty files

         if Event.Kind = DOC_END then
            return;
         elsif Event.Kind = ARRAY_START then
            Read_Type_Array;
         else
            Bad_Input;
         end if;

         --  There should be nothing more in the file

         Parse_Next_Event;

         if Event.Kind /= DOC_END then
            Bad_Input;
         end if;
      end Read_Doc;

      -------------
      -- Unquote --
      -------------

      function Unquote (S : String) return String is
      begin
         return S (S'First + 1 .. S'Last - 1);
      end Unquote;

      --------------------
      -- UI_From_String --
      --------------------

      function UI_From_String (S : String) return Valid_Uint is
         Storage_Mark : constant Uintp.Save_Mark := Mark;
         --  While building the numeric value we will create plenty of
         --  intermediate objects; they can be safely discarded afterwards.

         Result : Valid_Uint := Uint_0;
      begin
         for C of S loop
            Result := Result * Uint_10;
            Result :=
              Result + UI_From_Int (Character'Pos (C) - Character'Pos ('0'));
         end loop;

         Release_And_Save (Storage_Mark, Result);

         return Result;
      end UI_From_String;

   begin
      Read_Doc;
   end Read_JSON;

   ---------------------------------------
   -- Read_Data_Decomposition_JSON_File --
   ---------------------------------------

   procedure Read_Data_Decomposition_JSON_File is
      File_Names : String_Sets.Set;

   begin
      for J in Main_Unit .. Last_Unit loop

         --  Ignore units with no compilation unit. Those are pragma
         --  configuration units and they have no data decomposition.

         if Present (Cunit (J)) then
            declare
               Source_File_Name : constant String :=
                 Get_Name_String (Unit_File_Name (J));
               JSON_File_Name   : constant String :=
                 Source_File_Name & ".json";
            begin
               if not File_Names.Contains (Source_File_Name)
                 and then Ada.Directories.Exists (JSON_File_Name)
               then
                  Read_JSON (JSON_File_Name);
                  File_Names.Insert (Source_File_Name);
               end if;
            exception
               when E : others =>
                  Ada.Text_IO.Put_Line
                    (Ada.Text_IO.Standard_Error,
                     "error: ill-formed GNAT data representation file at "
                     & Ada.Exceptions.Exception_Message (E));
                  Ada.Text_IO.Put_Line
                    (Ada.Text_IO.Standard_Error,
                     "error: Try installing a more recent version of GNAT.");
                  Ada.Text_IO.Put_Line
                    (Ada.Text_IO.Standard_Error,
                     "error: As possible workarounds, remove GNAT from your "
                     & "PATH or use the switch -gnateT=<target.atp> to pass "
                     & "an explicit target parametrization file.");
                  GNAT.OS_Lib.OS_Exit (1);
            end;
         end if;
      end loop;
   end Read_Data_Decomposition_JSON_File;

end Gnat2Why.Data_Decomposition;
