------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        X T R E E _ W H Y _ A S T                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2021, AdaCore                     --
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

with Ada.Strings.Unbounded;      use Ada.Strings.Unbounded;
with GNAT.Case_Util;             use GNAT.Case_Util;
with Xkind_Tables;               use Xkind_Tables;
with Xtree_Tables;               use Xtree_Tables;
with Why.Sinfo;                  use Why.Sinfo;

package body Xtree_Why_AST is

   ------------------------
   -- Common auxiliaries --
   ------------------------

   function Strip_Prefix (Str : String) return String;
   --  Strip Gnat prefixes

   function Clean_Identifier (Str : String) return String;
   --  Replace dots by underscores

   type Variants is array (Integer range <>) of Unbounded_String;
   --  Variants of enumerate types from package Why.Sinfo

   ----------------------
   -- Clean_Identifier --
   ----------------------

   function Clean_Identifier (Str : String) return String is
      Res : String := Str;
   begin
      for Ix in Res'Range loop
         if Res (Ix) = '.' then
            Res (Ix) := '_';
         end if;
      end loop;
      return Res;
   end Clean_Identifier;

   ------------------
   -- Strip_Prefix --
   ------------------

   function Strip_Prefix (Str : String) return String is
      Start : Integer := Str'First;
      Str1  : String := Str;
   begin
      To_Lower (Str1);
      if Str1 in "source_ptr"
               | "symbol_set"
               | "string_sets.set"
               | "node_id"
               | "why_node_set"
      then
         return Str;
      else
         for J in Str'Range loop
            if Str (J) = '_' then
               Start := J + 1;
               exit;
            end if;
         end loop;
         return Str (Start .. Str'Last);
      end if;
   end Strip_Prefix;

   -----------------------------------
   -- Print Ada conversions to Json --
   -----------------------------------

   generic
      type T is (<>);
      Name : String;
   procedure Print_Ada_Enum_To_Json (O : in out Output_Record);
   --  This procedure, when instantiated, will print to O a serialization
   --  routine for an enumeration type T called Name. It assumes that
   --  individual enumeration literals are of the form "EW_Literal_Name".

   procedure Print_Ada_Why_Sinfo_Types_To_Json (O : in out Output_Record);

   procedure Print_Ada_Why_Node_To_Json (O : in out Output_Record);

   procedure Print_Ada_Opaque_Ids_To_Json (O : in out Output_Record);

   procedure Print_Ada_To_Json (O : in out Output_Record) is
   begin
      Print_Ada_Why_Sinfo_Types_To_Json (O);
      Print_Ada_Opaque_Ids_To_Json (O);
      Print_Ada_Why_Node_To_Json (O);
   end Print_Ada_To_Json;

   ----------------------------
   -- Print_Ada_Enum_To_Json --
   ----------------------------

   procedure Print_Ada_Enum_To_Json (O : in out Output_Record) is

      function EW_Mixed_Image (Val : T) return String;
      --  Given an enumeration value Val of the form "EW_Enum_Val" it returns
      --  its wide string representation with the "EW" prefix in upper case and
      --  the rest of the string in mixed case, so exactly as it would appear
      --  in gnat2why code.

      --------------------
      -- EW_Mixed_Image --
      --------------------

      function EW_Mixed_Image (Val : T) return String is
         Result : String := Val'Img;
      begin
         pragma Assert (Result (1 .. 3) = "EW_");
         To_Mixed (Result (4 .. Result'Last));
         return Result;
      end EW_Mixed_Image;

   --  Start of processing for Print_Ada_Enum_To_Json

   begin
      PL (O, "function " & Name & "_To_Json (Arg : " & Name & ")");
      PL (O, "   return JSON_Value;");
      NL (O);
      PL (O, "function " & Name & "_To_Json (Arg : " & Name & ")");
      PL (O, "return JSON_Value");
      begin
         Relative_Indent (O, 3);
         PL (O, "is (Create (Integer (case Arg is");
         begin
            Relative_Indent (O, 3);
            for E in T'Range loop
               P (O, "when " & EW_Mixed_Image (E) & " =>");
               P (O, Integer'Image (E'Enum_Rep));
               if E /= T'Last then
                  PL (O, ",");
               end if;
            end loop;
            Relative_Indent (O, -3);
         end;
         PL (O, ")));");
         Relative_Indent (O, -3);
      end;
      NL (O);
   end Print_Ada_Enum_To_Json;

   ---------------------------------------
   -- Print_Ada_Why_Sinfo_Types_To_Json --
   ---------------------------------------

   procedure Print_Ada_Why_Sinfo_Types_To_Json (O : in out Output_Record) is
      procedure Print_EW_Domain is new
        Print_Ada_Enum_To_Json (EW_Domain,      "EW_Domain");

      procedure Print_EW_Type is new
        Print_Ada_Enum_To_Json (EW_Type,        "EW_Type");

      procedure Print_EW_Literal is new
        Print_Ada_Enum_To_Json (EW_Literal,     "EW_Literal");

      procedure Print_EW_Theory_Type is new
        Print_Ada_Enum_To_Json (EW_Theory_Type, "EW_Theory_Type");

      procedure Print_EW_Clone_Type is new
        Print_Ada_Enum_To_Json (EW_Clone_Type,  "EW_Clone_Type");

      procedure Print_EW_Subst_Type is new
        Print_Ada_Enum_To_Json (EW_Subst_Type,  "EW_Subst_Type");

      procedure Print_EW_Connector is new
        Print_Ada_Enum_To_Json (EW_Connector,   "EW_Connector");

      procedure Print_EW_Assert_Kind is new
        Print_Ada_Enum_To_Json (EW_Assert_Kind, "EW_Assert_Kind");

   begin
      PL (O, "--  Why.Sinfo");

      NL (O);

      Print_EW_Domain      (O);
      Print_EW_Type        (O);
      Print_EW_Literal     (O);
      Print_EW_Theory_Type (O);
      Print_EW_Clone_Type  (O);
      Print_EW_Subst_Type  (O);
      Print_EW_Connector   (O);
      Print_EW_Assert_Kind (O);

   end Print_Ada_Why_Sinfo_Types_To_Json;

   --------------------------------
   -- Print_Ada_Why_Node_To_Json --
   --------------------------------

   procedure Print_Ada_Why_Node_To_Json (O : in out Output_Record) is
   begin
      PL (O, "Why_Node_Counter : Integer := 0;");
      NL (O);
      PL (O, "function Why_Node_To_Json (Node : Why_Node) " &
            "return JSON_Value is");
      begin
         Relative_Indent (O, 3);
         PL (O, "Res : constant JSON_Value := Create (Empty_Array);");
         Relative_Indent (O, -3);
      end;
      PL (O, "begin");
      begin
         Relative_Indent (O, 3);
         PL (O, "Why_Node_Counter := Why_Node_Counter + 1;");
         PL (O, "Append (Res, Create (Why_Node_Kind'Image (Node.Kind)));");
         PL (O, "Append (Res, Create (Why_Node_Counter));");
         for FI of Common_Fields.Fields loop
            declare
               Typ_Name : constant String :=
                 Clean_Identifier (Type_Name (FI, Opaque));
            begin
               PL (O, "Append (Res, " &
                     Typ_Name & "_To_Json (Node." & Field_Name (FI) &
                     "));");
            end;
         end loop;
         PL (O, "case Node.Kind is");
         begin
            Relative_Indent (O, 3);
            for Kind in Why_Tree_Info'Range loop
               PL (O, "when " & Mixed_Case_Name (Kind) & " =>");
               Relative_Indent (O, 3);
               if Why_Tree_Info (Kind).Fields.Is_Empty then
                  PL (O, "null;");
               else
                  for FI of Why_Tree_Info (Kind).Fields loop
                     declare
                        Field_Type : constant String :=
                          Clean_Identifier (Type_Name (FI, Opaque));
                     begin
                        PL (O, "Append (Res, " & Field_Type & "_To_Json");
                        PL (O, "   (Node." & Field_Name (FI) & "));");
                     end;
                  end loop;
               end if;
               Relative_Indent (O, -3);
            end loop;
            Relative_Indent (O, -3);
         end;
         PL (O, "end case;");
         PL (O, "return Res;");
         Relative_Indent (O, -3);
      end;
      PL (O, "end Why_Node_To_Json;");
   end Print_Ada_Why_Node_To_Json;

   ----------------------------------
   -- Print_Ada_Opaque_Ids_To_Json --
   ----------------------------------

   procedure Print_Ada_Opaque_Ids_To_Json (O : in out Output_Record) is
      use String_Lists;
      use Class_Lists;

      procedure Process_One_Node_Kind (Position : String_Lists.Cursor);
      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor);
      procedure Print_Subtypes (Prefix : String);

      ----------------------------
      -- Process_One_Class_Kind --
      ----------------------------

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor) is
         CI : constant Class_Info := Class_Lists.Element (Position);
      begin
         Print_Subtypes (Class_Name (CI));
      end Process_One_Class_Kind;

      ---------------------------
      -- Process_One_Node_Kind --
      ---------------------------

      procedure Process_One_Node_Kind (Position : String_Lists.Cursor) is
         S : constant Xkind_Tables.String_Access :=
           String_Lists.Element (Position);
      begin
         Print_Subtypes (S.all);
      end Process_One_Node_Kind;

      --------------------
      -- Print_Subtypes --
      --------------------

      procedure Print_Subtypes (Prefix : String) is
      begin
         for Multiplicity in Id_Multiplicity'Range loop
            declare
               Name : constant String :=
                 Id_Subtype (Prefix, Opaque, Multiplicity);
               Why_Node_Name : constant String :=
                 Id_Subtype ("Why_Node", Derived, Multiplicity);
            begin
               PL (O, "function " & Name & "_To_Json");
               begin
                  Relative_Indent (O, 3);
                  PL (O, "(Arg : " & Name & ")");
                  PL (O, "return JSON_Value;");
                  Relative_Indent (O, -3);
               end;
               NL (O);
               PL (O, "function " & Name & "_To_Json");
               begin
                  Relative_Indent (O, 3);
                  PL (O, "(Arg : " & Name & ")");
                  PL (O, "return JSON_Value");
                  PL (O, "is (" & Why_Node_Name & "_To_Json (Arg));");
                  Relative_Indent (O, -3);
               end;
               NL (O);
            end;
         end loop;
      end Print_Subtypes;

   --  Start of processing for Print_Ada_Opaque_Ids_To_Json

   begin
      Kinds.Iterate (Process_One_Node_Kind'Access);
      Classes.Iterate (Process_One_Class_Kind'Access);
   end Print_Ada_Opaque_Ids_To_Json;

   -----------------------
   -- OCaml auxiliaries --
   -----------------------

   function OCaml_Lower_Identifier (Str : String) return String;

   function OCaml_Upper_Identifier (Str : String) return String;

   function Kind_To_String (Kind : Why_Node_Kind) return String;

   ----------------------------
   -- OCaml_Lower_Identifier --
   ----------------------------

   function OCaml_Lower_Identifier (Str : String) return String is
      Str1 : String := Clean_Identifier (Str);
   begin
      To_Lower (Str1);
      declare
         Str2 : constant String :=
           (if Str1 = "boolean" then
               "bool"
           elsif Str1 = "type" then
              "type_"
           elsif Str1 = "module" then
              "module_"
           elsif Str1 = "assert" then
              "assert_"
           elsif Str1 = "to" then
              "to_"
           else
              Str1);
      begin
         return Str2;
      end;
   end OCaml_Lower_Identifier;

   ----------------------------
   -- OCaml_Upper_Identifier --
   ----------------------------

   function OCaml_Upper_Identifier (Str : String) return String is
      Str1 : String := Clean_Identifier (Str);
   begin
      To_Lower (Str1);
      if Str1'Length > 0 then
         Str1 (Str1'First) := To_Upper (Str1 (Str1'First));
      end if;
      return Str1;
   end OCaml_Upper_Identifier;

   --------------------
   -- Kind_To_String --
   --------------------

   function Kind_To_String (Kind : Why_Node_Kind) return String is
     (Strip_Prefix (Why_Node_Kind'Image (Kind)));

   -----------------------------------
   -- Print OCaml type declarations --
   -----------------------------------

   ---------------------------------
   -- Print_OCaml_Why_Sinfo_Types --
   ---------------------------------

   procedure Print_OCaml_Why_Sinfo_Types (O : in out Output_Record) is
   begin
      PL (O, "(* Why.Sinfo *)");
      NL (O);

      PL (O, "type odomain =");
      Relative_Indent (O, 2);
      for X in EW_ODomain'Range loop
         PL (O, "| " & OCaml_Upper_Identifier
               (Strip_Prefix (EW_ODomain'Image (X))));
      end loop;
      Relative_Indent (O, -2);
      NL (O);

      PL (O, "type domain =");
      Relative_Indent (O, 2);
      for X in EW_Domain'Range loop
         PL (O, "| " & OCaml_Upper_Identifier
               (Strip_Prefix (EW_Domain'Image (X))));
      end loop;
      Relative_Indent (O, -2);
      NL (O);

      PL (O, "type type_ =");
      Relative_Indent (O, 2);
      for X in EW_Type'Range loop
         PL (O, "| " & OCaml_Upper_Identifier
               (Strip_Prefix (EW_Type'Image (X))));
      end loop;
      Relative_Indent (O, -2);
      NL (O);

      PL (O, "type literal =");
      Relative_Indent (O, 2);
      for X in EW_Literal'Range loop
         PL (O, "| " & OCaml_Upper_Identifier
               (Strip_Prefix (EW_Literal'Image (X))));
      end loop;
      Relative_Indent (O, -2);
      NL (O);

      PL (O, "type theory_type =");
      Relative_Indent (O, 2);
      for X in EW_Theory_Type'Range loop
         PL (O, "| " & OCaml_Upper_Identifier
               (Strip_Prefix (EW_Theory_Type'Image (X))));
      end loop;
      Relative_Indent (O, -2);
      NL (O);

      PL (O, "type clone_type =");
      Relative_Indent (O, 2);
      for X in EW_Clone_Type'Range loop
         PL (O, "| " & OCaml_Upper_Identifier
               (Strip_Prefix (EW_Clone_Type'Image (X))));
      end loop;
      Relative_Indent (O, -2);
      NL (O);

      PL (O, "type subst_type =");
      Relative_Indent (O, 2);
      for X in EW_Subst_Type'Range loop
         PL (O, "| " & OCaml_Upper_Identifier
               (Strip_Prefix (EW_Subst_Type'Image (X))));
      end loop;
      Relative_Indent (O, -2);
      NL (O);

      PL (O, "type connector =");
      Relative_Indent (O, 2);
      for X in EW_Connector'Range loop
         PL (O, "| " & OCaml_Upper_Identifier
               (Strip_Prefix (EW_Connector'Image (X))));
      end loop;
      Relative_Indent (O, -2);
      NL (O);

      PL (O, "type assert_kind =");
      Relative_Indent (O, 2);
      for X in EW_Assert_Kind'Range loop
         PL (O, "| " & OCaml_Upper_Identifier
               (Strip_Prefix (EW_Assert_Kind'Image (X))));
      end loop;
      Relative_Indent (O, -2);
   end Print_OCaml_Why_Sinfo_Types;

   ----------------------
   -- Print_OCaml_Tags --
   ----------------------

   procedure Print_OCaml_Tags (O : in out Output_Record) is
      procedure Print_Kind_Tag_Type (Position : String_Lists.Cursor);
      procedure Print_Class_Tag_Type (Position : Class_Lists.Cursor);

      -------------------------
      -- Print_Kind_Tag_Type --
      -------------------------

      procedure Print_Kind_Tag_Type (Position : String_Lists.Cursor) is
         S : constant Xkind_Tables.String_Access :=
           String_Lists.Element (Position);
         Name : constant String := Strip_Prefix (S.all);
         Type_Tag_Name : constant String :=
           OCaml_Lower_Identifier (Name & "_tag");
         Variant_Name  : constant String := OCaml_Upper_Identifier (Name);
      begin
         if S.all /= "W_Unused_At_Start" then
            PL (O, "type " & Type_Tag_Name & " = [`" & Variant_Name & "]");
         end if;
      end Print_Kind_Tag_Type;

      --------------------------
      -- Print_Class_Tag_Type --
      --------------------------

      procedure Print_Class_Tag_Type (Position : Class_Lists.Cursor) is
         Class : constant Class_Info := Class_Lists.Element (Position);
         Type_Tag_Name : constant String :=
           OCaml_Lower_Identifier (Strip_Prefix (Class.Name.all) & "_tag");
      begin
         PL (O, "type " & Type_Tag_Name & " = [");
         for Kind in Class_First (Class) .. Class_Last (Class) loop
            P (O, " | ");
            PL (O, "`" & OCaml_Upper_Identifier (Kind_To_String (Kind)));
         end loop;
         PL (O, "]");
      end Print_Class_Tag_Type;

   --  Start of processing for Print_OCaml_Tags

   begin
      PL (O, "(* Kind tags *)");
      NL (O);
      Kinds.Iterate (Print_Kind_Tag_Type'Access);
      NL (O);
      PL (O, "(* Class tags *)");
      NL (O);
      Classes.Iterate (Print_Class_Tag_Type'Access);
   end Print_OCaml_Tags;

   ----------------------------
   -- Print_OCaml_Opaque_Ids --
   ----------------------------

   procedure Print_OCaml_Opaque_Ids (O : in out Output_Record) is
      use String_Lists;
      use Class_Lists;

      procedure Print_Kind_Subtypes (Position : String_Lists.Cursor);
      procedure Print_Class_Subtypes (Position : Class_Lists.Cursor);
      procedure Print_Subtypes (Prefix : String);

      -------------------------
      -- Print_Kind_Subtypes --
      -------------------------

      procedure Print_Kind_Subtypes (Position : String_Lists.Cursor) is
         S : constant Xkind_Tables.String_Access :=
           String_Lists.Element (Position);
      begin
         if S.all /= "W_Unused_At_Start" then
            Print_Subtypes (S.all);
         end if;
         if Position /= Kinds.Last then
            NL (O);
         end if;
      end Print_Kind_Subtypes;

      --------------------------
      -- Print_Class_Subtypes --
      --------------------------

      procedure Print_Class_Subtypes (Position : Class_Lists.Cursor) is
         CI : constant Class_Info := Class_Lists.Element (Position);
      begin
         Print_Subtypes (Class_Name (CI));
         if Position /= Classes.Last then
            NL (O);
         end if;
      end Print_Class_Subtypes;

      --------------------
      -- Print_Subtypes --
      --------------------

      procedure Print_Subtypes (Prefix : String) is
      begin
         for Multiplicity in Id_Multiplicity'Range loop
            declare
               Name : constant String :=
                 OCaml_Lower_Identifier
                   (Strip_Prefix
                      (Id_Subtype (Prefix, Derived, Multiplicity)));
               Alias : constant String :=
                 OCaml_Lower_Identifier
                   (Id_Subtype ("why_node", Derived, Multiplicity));
               Type_Tag_Str : constant String :=
                 OCaml_Lower_Identifier (Strip_Prefix (Prefix) & "_tag");
            begin
               PL (O, "and " & Name & " = " & Type_Tag_Str & " " & Alias);
            end;
         end loop;
      end Print_Subtypes;

   --  Start of processing for Print_OCaml_Opaque_Ids

   begin
      PL (O, "(* Kind nodes *)");
      Kinds.Iterate (Print_Kind_Subtypes'Access);
      NL (O);
      PL (O, "(* Class nodes *)");
      NL (O);
      Classes.Iterate (Print_Class_Subtypes'Access);
   end Print_OCaml_Opaque_Ids;

   -------------------------------
   -- Print_OCaml_Why_Node_Type --
   -------------------------------

   procedure Print_OCaml_Why_Node_Type (O : in out Output_Record) is
      use Xtree_Tables.Node_Lists;
   begin
      PL (O, "(* Why_Node *)");
      NL (O);
      PL (O, "type 'a why_node = " &
            "{ info : why_node_info ; desc: 'a why_node_desc }");
      NL (O);
      P (O, "and why_node_info = {");
      declare
         First : Boolean := True;
      begin
         P (O, "id: int; ");
         for FI of Common_Fields.Fields loop
            declare
               Field : constant String :=
                 OCaml_Lower_Identifier (Strip_Prefix (Field_Name (FI)));
               Typ   : constant String :=
                 OCaml_Lower_Identifier
                   (Strip_Prefix (Type_Name (FI, Opaque)));
            begin
               if not First then
                  P (O, "; ");
               end if;
               P (O, Field & ": " & Typ);
               First := False;
            end;
         end loop;
      end;
      PL (O, "}");
      NL (O);
      PL (O, "and 'a why_node_desc =");
      Relative_Indent (O, 2);
      for Kind in Why_Tree_Info'Range loop
         if Kind /= W_Unused_At_Start then
            P (O, "| " & OCaml_Upper_Identifier (Kind_To_String (Kind)));
            P (O, " : ");
            declare
               First : Boolean := True;
               Has_Fields : constant Boolean :=
                 not Is_Empty (Why_Tree_Info (Kind).Fields);
            begin
               Relative_Indent (O, 4);
               if Has_Fields then
                  P (O, "{");
                  Relative_Indent (O, 2);
                  for FI of Why_Tree_Info (Kind).Fields loop
                     declare
                        Field : constant String :=
                          OCaml_Lower_Identifier
                            (Strip_Prefix (Field_Name (FI)));
                        Typ   : constant String :=
                          OCaml_Lower_Identifier
                            (Strip_Prefix (Type_Name (FI, Derived)));
                     begin
                        if not First then
                           P (O, "; ");
                        end if;
                        P (O, Field & ": " & Typ);
                        First := False;
                     end;
                  end loop;
                  Relative_Indent (O, -2);
                  P (O, "} -> ");
               end if;
               P (O, "[> " &
                    OCaml_Lower_Identifier (Kind_To_String (Kind) & "_tag") &
                    "] why_node_desc");
               NL (O);
               Relative_Indent (O, -4);
            end;
         end if;
      end loop;
      Relative_Indent (O, -2);
   end Print_OCaml_Why_Node_Type;

   --------------------------------------
   -- Print OCaml conversion from Json --
   --------------------------------------

   function OCaml_Field_Names (Fields : Node_Lists.List) return Variants;
   function OCaml_Field_Types (Fields : Node_Lists.List; Suffix : String)
                               return Variants;

   -----------------------
   -- OCaml_Field_Names --
   -----------------------

   function OCaml_Field_Names (Fields : Node_Lists.List) return Variants is
      use Node_Lists;
      Res : Variants (1 .. Integer (Length (Fields)));
      C   : Cursor := First (Fields);
   begin
      for I in Res'Range loop
         declare
            Field : constant Unbounded_String :=
              To_Unbounded_String
                (OCaml_Lower_Identifier
                   (Strip_Prefix (Field_Name (Element (C)))));
         begin
            Res (I) := Field;
            Next (C);
         end;
      end loop;
      return Res;
   end OCaml_Field_Names;

   -----------------------
   -- OCaml_Field_Types --
   -----------------------

   function OCaml_Field_Types
     (Fields : Node_Lists.List; Suffix : String) return Variants
   is
      use Node_Lists;
      Res : Variants (1 .. Integer (Length (Fields)));
      C   : Cursor := First (Fields);
   begin
      for I in Res'Range loop
         declare
            Typ : constant Unbounded_String :=
              To_Unbounded_String
                (OCaml_Lower_Identifier
                   (Strip_Prefix (Type_Name (Element (C), Opaque)) & Suffix));
         begin
            Res (I) := Typ;
            Next (C);
         end;
      end loop;
      return Res;
   end OCaml_Field_Types;

   ------------------------------------
   -- Print_OCaml_Why_Node_From_Json --
   ------------------------------------

   procedure Print_OCaml_Why_Node_From_Json (O : in out Output_Record) is
      Common_Field_Names : constant Variants :=
        OCaml_Field_Names (Common_Fields.Fields);
      Common_Field_Converters : constant Variants :=
        OCaml_Field_Types (Common_Fields.Fields, "_from_json");
   begin
      PL (O, "let rec why_node_from_json : 'a why_node from_json = function");
      begin
         Relative_Indent (O, 2);
         for Kind in Why_Tree_Info'Range loop
            declare
               Kind_Str : constant String := Why_Node_Kind'Image (Kind);
               Info     : constant Why_Node_Info := Why_Tree_Info (Kind);
               Variant_Name : constant String :=
                 OCaml_Upper_Identifier
                   (Strip_Prefix (Why_Node_Kind'Image (Kind)));
               Variant_Field_Names : constant Variants :=
                 OCaml_Field_Names (Info.Fields);
               Variant_Field_Converters : constant Variants :=
                 OCaml_Field_Types (Info.Fields, "_from_json");
            begin
               if Kind /= W_Unused_At_Start then
                  --  Pattern matching
                  P (O, "| `List [");
                  P (O, "`String """ & Kind_Str & """");
                  P (O, "; id");
                  for I in Common_Field_Names'Range loop
                     P (O, "; " & To_String (Common_Field_Names (I)));
                  end loop;
                  for I in Variant_Field_Names'Range loop
                     P (O, "; " & To_String (Variant_Field_Names (I)));
                  end loop;
                  PL (O, "] ->");
                  begin
                     --  Generate variant
                     Relative_Indent (O, 2);
                     PL (O, "let info = {");
                     begin
                        Relative_Indent (O, 2);
                        PL (O, "id = int_from_json id;");
                        for I in Common_Field_Names'Range loop
                           P (O, To_String (Common_Field_Names (I)));
                           P (O, " = ");
                           P (O, To_String (Common_Field_Converters (I)));
                           P (O, " ");
                           P (O, To_String (Common_Field_Names (I)));
                           PL (O, ";");
                        end loop;
                        Relative_Indent (O, -2);
                     end;
                     PL (O, "} in");
                     P (O, "let desc = " & Variant_Name);
                     if Variant_Field_Names'Length > 0 then
                        PL (O, " {");
                        begin
                           Relative_Indent (O, 2);
                           for I in Variant_Field_Names'Range loop
                              P (O, To_String (Variant_Field_Names (I)));
                              P (O, " = ");
                              P (O, To_String (Variant_Field_Converters (I)));
                              P (O, " ");
                              P (O, To_String (Variant_Field_Names (I)));
                              PL (O, ";");
                           end loop;
                           Relative_Indent (O, -2);
                        end;
                        P (O, "}");
                     end if;
                     PL (O, " in");
                     PL (O, "{info; desc}");
                     Relative_Indent (O, -2);
                  end;
               end if;
            end;
         end loop;
         PL (O, "| json ->");
         PL (O, "  unexpected_json ""why_node"" json");
         Relative_Indent (O, -2);
      end;
   end Print_OCaml_Why_Node_From_Json;

   --------------------------------------
   -- Print_OCaml_Opaque_Ids_From_Json --
   --------------------------------------

   procedure Print_OCaml_Opaque_Ids_From_Json (O : in out Output_Record) is
      use String_Lists;
      use Class_Lists;

      procedure Process_One_Node_Kind (Position : String_Lists.Cursor);
      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor);
      procedure Print_Subtypes (Prefix : String);

      ---------------------------
      -- Process_One_Node_Kind --
      ---------------------------

      procedure Process_One_Node_Kind (Position : String_Lists.Cursor) is
         S : constant Xkind_Tables.String_Access :=
           String_Lists.Element (Position);
      begin
         if S.all /= "W_Unused_At_Start" then
            Print_Subtypes (S.all);
         end if;
         if Position /= Kinds.Last then
            NL (O);
         end if;
      end Process_One_Node_Kind;

      ----------------------------
      -- Process_One_Class_Kind --
      ----------------------------

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor) is
         CI : constant Class_Info := Class_Lists.Element (Position);
      begin
         Print_Subtypes (Class_Name (CI));
         if Position /= Classes.Last then
            NL (O);
         end if;
      end Process_One_Class_Kind;

      --------------------
      -- Print_Subtypes --
      --------------------

      procedure Print_Subtypes (Prefix : String) is
      begin
         for Multiplicity in Id_Multiplicity'Range loop
            declare
               Prefix_Mult : constant String :=
                 Id_Subtype (Prefix, Opaque, Multiplicity);
               Name        : constant String :=
                 OCaml_Lower_Identifier
                   (Strip_Prefix (Prefix_Mult) & "_from_json");
               Alias       : constant String :=
                 OCaml_Lower_Identifier
                   (Id_Subtype ("why_node", Derived, Multiplicity) &
                    "_from_json");
               Coercion    : constant String :=
                 OCaml_Lower_Identifier (Strip_Prefix (Prefix) & "_coercion");
            begin
               PL (O, "and " & Name & " json =" & "  "
                     & Alias & " " & Coercion
                     & " json");
            end;
         end loop;
      end Print_Subtypes;

   --  Start of processing for Print_OCaml_Opaque_Ids_From_Json

   begin
      PL (O, "(* Opaque tags from json *)");
      Kinds.Iterate (Process_One_Node_Kind'Access);
      NL (O);
      PL (O, "(* Opaque classes from json *)");
      NL (O);
      Classes.Iterate (Process_One_Class_Kind'Access);
   end Print_OCaml_Opaque_Ids_From_Json;

   ---------------------------
   -- Print_OCaml_Coercions --
   ---------------------------

   procedure Print_OCaml_Coercions (O : in out Output_Record) is
      use String_Lists;
      use Class_Lists;

      procedure Print_Kind_Tag_Coercion (Position : String_Lists.Cursor);

      procedure Print_Kind_Class_Coercion (Position : Class_Lists.Cursor);

      -----------------------------
      -- Print_Kind_Tag_Coercion --
      -----------------------------

      procedure Print_Kind_Tag_Coercion (Position : String_Lists.Cursor) is
         S : constant Xkind_Tables.String_Access :=
           String_Lists.Element (Position);
         Name : constant String := Strip_Prefix (S.all);
         Coercion : constant String :=
           OCaml_Lower_Identifier (Name & "_coercion");
         Res_Type : constant String :=
           OCaml_Lower_Identifier (Name & "_tag") & " why_node";
         Variant  : constant String :=
           OCaml_Upper_Identifier (Name);
      begin
         if S.all /= "W_Unused_At_Start" then
            PL (O, "let " & Coercion & " (node : any_node_tag why_node) : " &
                  Res_Type & " =");
            begin
               Relative_Indent (O, 2);
               PL (O, "match node.desc with");
               P (O, "| " & Variant & " _ as desc ->");
               PL (O, " {info=node.info; desc}");
               PL (O, "| _ -> invalid_arg """ & Coercion & """");
               Relative_Indent (O, -2);
            end;
            NL (O);
         end if;
      end Print_Kind_Tag_Coercion;

      -------------------------------
      -- Print_Kind_Class_Coercion --
      -------------------------------

      procedure Print_Kind_Class_Coercion (Position : Class_Lists.Cursor) is
         Class : constant Class_Info := Class_Lists.Element (Position);
         Coercion : constant String := OCaml_Lower_Identifier
           (Strip_Prefix (Class.Name.all) & "_coercion");
         Res_Type : constant String := OCaml_Lower_Identifier
           (Strip_Prefix (Class.Name.all) & "_tag")
           & " why_node";
      begin
         P (O, "let " & Coercion);
         P (O, " (node : any_node_tag why_node) : ");
         PL (O, Res_Type & " =");
         begin
            Relative_Indent (O, 2);
            PL (O, "match node.desc with");
            for Kind in Class_First (Class) .. Class_Last (Class) loop
               P (O, "| " & OCaml_Upper_Identifier (Kind_To_String (Kind)));
               PL (O, " _ as desc -> {info=node.info; desc}");
            end loop;
            PL (O, "| _ -> invalid_arg """ & Coercion & """");
            PL (O, "[@@warning ""-11""]");
            Relative_Indent (O, -2);
         end;
         NL (O);
      end Print_Kind_Class_Coercion;

   --  Start of processing for Print_OCaml_Coercions

   begin
      PL (O, "(* Tag coercions *)");
      Kinds.Iterate (Print_Kind_Tag_Coercion'Access);
      NL (O);
      PL (O, "(* Class coercions *)");
      Classes.Iterate (Print_Kind_Class_Coercion'Access);
   end Print_OCaml_Coercions;

   generic
      type T is (<>);
      Name : String;
   procedure Print_OCaml_Enum_From_Json (O : in out Output_Record);

   --------------------------------
   -- Print_OCaml_Enum_From_Json --
   --------------------------------

   procedure Print_OCaml_Enum_From_Json (O : in out Output_Record) is
      Func_Name : constant String :=
        OCaml_Lower_Identifier (Strip_Prefix (Name) & "_from_json");
      Type_Name : constant String :=
        OCaml_Lower_Identifier (Strip_Prefix (Name));
   begin
      PL (O, "let " & Func_Name & " : " & Type_Name & " from_json = function");
      begin
         Relative_Indent (O, 2);
         for E in T'Range loop
            P (O, "| `Int" & Integer'Image (E'Enum_Rep));
            PL (O, " -> " & OCaml_Upper_Identifier (Strip_Prefix (E'Img)));
         end loop;
         PL (O, "| json -> unexpected_json "
               & """" & Type_Name & """ json");
         Relative_Indent (O, -2);
      end;
      NL (O);
   end Print_OCaml_Enum_From_Json;

   -------------------------------------------
   -- Print_OCaml_Why_Sinfo_Types_From_Json --
   -------------------------------------------

   procedure Print_OCaml_Why_Sinfo_Types_From_Json
     (O : in out Output_Record)
   is
      procedure Print_EW_Domain is new
        Print_OCaml_Enum_From_Json (EW_Domain,      "EW_Domain");

      procedure Print_EW_Type is new
        Print_OCaml_Enum_From_Json (EW_Type,        "EW_Type");

      procedure Print_EW_Literal is new
        Print_OCaml_Enum_From_Json (EW_Literal,     "EW_Literal");

      procedure Print_EW_Theory_Type is new
        Print_OCaml_Enum_From_Json (EW_Theory_Type, "EW_Theory_Type");

      procedure Print_EW_Clone_Type is new
        Print_OCaml_Enum_From_Json (EW_Clone_Type,  "EW_Clone_Type");

      procedure Print_EW_Subst_Type is new
        Print_OCaml_Enum_From_Json (EW_Subst_Type,  "EW_Subst_Type");

      procedure Print_EW_Connector is new
        Print_OCaml_Enum_From_Json (EW_Connector,   "EW_Connector");

      procedure Print_EW_Assert_Kind is new
        Print_OCaml_Enum_From_Json (EW_Assert_Kind, "EW_Assert_Kind");

   begin
      PL (O, "(* Why.Sinfo *)");
      NL (O);

      Print_EW_Domain      (O);
      Print_EW_Type        (O);
      Print_EW_Literal     (O);
      Print_EW_Theory_Type (O);
      Print_EW_Clone_Type  (O);
      Print_EW_Subst_Type  (O);
      Print_EW_Connector   (O);
      Print_EW_Assert_Kind (O);

   end Print_OCaml_Why_Sinfo_Types_From_Json;

end Xtree_Why_AST;
