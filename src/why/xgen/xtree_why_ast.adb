------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        X T R E E _ W H Y _ A S T                         --
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
with Ada.Strings.Unbounded;      use Ada.Strings.Unbounded;
with GNAT.Case_Util;             use GNAT.Case_Util;
with Xkind_Tables;               use Xkind_Tables;
with Xtree_Tables;               use Xtree_Tables;
with Why.Sinfo;                  use Why.Sinfo;
with Xkind_Tables;
with Xtree_Tables;
with Utils;

package body Xtree_Why_AST is

   ------------------------
   -- Common auxiliaries --
   ------------------------

   function To_Wide_String (S : Unbounded_String) return Wide_String;
   function To_Unbounded_String (S : Wide_String) return Unbounded_String;

   --  Strip Gnat prefixes
   function Strip_Prefix (Str : String) return String;
   function Strip_Prefix (Str : Wide_String) return Wide_String;

   --  Replace dots by underscores
   function Clean_Identifier (Str : String) return String;

   --  Variants of enumerate types from package Why.Sinfo
   type Variants is array (Integer range <>) of Unbounded_String;

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

   -------------------------------------
   -- To_Wide_String (Unbound_String) --
   -------------------------------------

   function To_Wide_String (S : Unbounded_String) return Wide_String is
     (To_Wide_String (To_String (S)));

   ---------------------------------------
   -- To_Unbounded_String (Wide_String) --
   ---------------------------------------

   function To_Unbounded_String (S : Wide_String) return Unbounded_String is
     (To_Unbounded_String (To_String (S)));

   ------------------
   -- Strip_Prefix --
   ------------------

   function Strip_Prefix (Str : String) return String is
      Start : Integer := Str'First;
      Str1  : String := Str;
   begin
      To_Lower (Str1);
      if Str1 = "source_ptr" or else Str1 = "symbol_set" or else
        Str1 = "string_sets.set" or else Str1 = "node_id" or else
        Str1 = "why_node_set"
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

   function Strip_Prefix (Str : Wide_String) return Wide_String is
     (To_Wide_String (Strip_Prefix (To_String (Str))));

   -----------------------------------
   -- Print Ada conversions to Json --
   -----------------------------------

   procedure Print_Ada_Enum_To_Json
     (O    : in out Output_Record;
      Name : Wide_String;
      Vars : Variants);

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

   procedure Print_Ada_Enum_To_Json
     (O    : in out Output_Record;
      Name : Wide_String;
      Vars : Variants)
   is
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
            for I in Vars'Range loop
               P (O, "when " & To_Wide_String (Vars (I)) & " =>");
               --  P (O, """" & To_Wide_String (Vars (I)) & """");
               P (O, To_Wide_String (Integer'Image (I)));
               if I /= Vars'Last then
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

      function To_Unbounded_Mixed_Case (S : String) return Unbounded_String;
      --  ??? what does this function do?

      -----------------------------
      -- To_Unbounded_Mixed_Case --
      -----------------------------

      function To_Unbounded_Mixed_Case (S : String) return Unbounded_String is
         S1 : String := S;
      begin
         To_Mixed (S1);
         S1 (2) := To_Upper (S1 (2));
         return To_Unbounded_String (S1);
      end To_Unbounded_Mixed_Case;

   --  Start of processing for Print_Ada_Why_Sinfo_Types_To_Json

   begin
      PL (O, "--  Why.Sinfo");

      NL (O);
      declare
         EW_Domain_Variants : Variants
           (EW_Domain'Pos (EW_Domain'First) ..
            EW_Domain'Pos (EW_Domain'Last));
      begin
         for I in EW_Domain_Variants'Range loop
            EW_Domain_Variants (I) := To_Unbounded_Mixed_Case
              (EW_Domain'Image (EW_Domain'Val (I)));
         end loop;
         Print_Ada_Enum_To_Json (O, "EW_Domain", EW_Domain_Variants);
      end;

      declare
         EW_Type_Variants : Variants
           (EW_Type'Pos (EW_Type'First) ..
            EW_Type'Pos (EW_Type'Last));
      begin
         for I in EW_Type_Variants'Range loop
            EW_Type_Variants (I) := To_Unbounded_Mixed_Case
              (EW_Type'Image (EW_Type'Val (I)));
         end loop;
         Print_Ada_Enum_To_Json (O, "EW_Type", EW_Type_Variants);
      end;

      declare
         EW_Literal_Variants : Variants
           (EW_Literal'Pos (EW_Literal'First) ..
            EW_Literal'Pos (EW_Literal'Last));
      begin
         for I in EW_Literal_Variants'Range loop
            EW_Literal_Variants (I) := To_Unbounded_Mixed_Case
              (EW_Literal'Image (EW_Literal'Val (I)));
         end loop;
         Print_Ada_Enum_To_Json (O, "EW_Literal", EW_Literal_Variants);
      end;

      declare
         EW_Theory_Type_Variants : Variants
           (EW_Theory_Type'Pos (EW_Theory_Type'First) ..
            EW_Theory_Type'Pos (EW_Theory_Type'Last));
      begin
         for I in EW_Theory_Type_Variants'Range loop
            EW_Theory_Type_Variants (I) := To_Unbounded_Mixed_Case
              (EW_Theory_Type'Image (EW_Theory_Type'Val (I)));
         end loop;
         Print_Ada_Enum_To_Json (O, "EW_Theory_Type", EW_Theory_Type_Variants);
      end;

      declare
         EW_Clone_Type_Variants : Variants
           (EW_Clone_Type'Pos (EW_Clone_Type'First) ..
            EW_Clone_Type'Pos (EW_Clone_Type'Last));
      begin
         for I in EW_Clone_Type_Variants'Range loop
            EW_Clone_Type_Variants (I) := To_Unbounded_Mixed_Case
              (EW_Clone_Type'Image (EW_Clone_Type'Val (I)));
         end loop;
         Print_Ada_Enum_To_Json (O, "EW_Clone_Type", EW_Clone_Type_Variants);
      end;

      declare
         EW_Subst_Type_Variants : Variants
           (EW_Subst_Type'Pos (EW_Subst_Type'First) ..
            EW_Subst_Type'Pos (EW_Subst_Type'Last));
      begin
         for I in EW_Subst_Type_Variants'Range loop
            EW_Subst_Type_Variants (I) := To_Unbounded_Mixed_Case
              (EW_Subst_Type'Image (EW_Subst_Type'Val (I)));
         end loop;
         Print_Ada_Enum_To_Json (O, "EW_Subst_Type", EW_Subst_Type_Variants);
      end;

      declare
         EW_Connector_Variants : Variants
           (EW_Connector'Pos (EW_Connector'First) ..
            EW_Connector'Pos (EW_Connector'Last));
      begin
         for I in EW_Connector_Variants'Range loop
            EW_Connector_Variants (I) := To_Unbounded_Mixed_Case
              (EW_Connector'Image (EW_Connector'Val (I)));
         end loop;
         Print_Ada_Enum_To_Json (O, "EW_Connector", EW_Connector_Variants);
      end;

      declare
         EW_Assert_Kind_Variants : Variants
           (EW_Assert_Kind'Pos (EW_Assert_Kind'First) ..
            EW_Assert_Kind'Pos (EW_Assert_Kind'Last));
      begin
         for I in EW_Assert_Kind_Variants'Range loop
            EW_Assert_Kind_Variants (I) := To_Unbounded_Mixed_Case
              (EW_Assert_Kind'Image (EW_Assert_Kind'Val (I)));
         end loop;
         Print_Ada_Enum_To_Json (O, "EW_Assert_Kind", EW_Assert_Kind_Variants);
      end;
   end Print_Ada_Why_Sinfo_Types_To_Json;

   --------------------------------
   -- Print_Ada_Why_Node_To_Json --
   --------------------------------

   procedure Print_Ada_Why_Node_To_Json (O : in out Output_Record) is
   begin
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
         PL (O, "Append (Res, Create (Why_Node_Kind'Image (Node.Kind)));");
         for FI of Common_Fields.Fields loop
            declare
               Typ_Name : Wide_String := To_Wide_String
                 (Clean_Identifier
                    (To_String (Type_Name (FI, Opaque))));
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
                        Field_Type : Wide_String := To_Wide_String
                          (Clean_Identifier
                             (To_String (Type_Name (FI, Opaque))));
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
      procedure Print_Subtypes (Prefix : Wide_String);

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
         S : constant Wide_String_Access := String_Lists.Element (Position);
      begin
         Print_Subtypes (S.all);
      end Process_One_Node_Kind;

      --------------------
      -- Print_Subtypes --
      --------------------

      procedure Print_Subtypes (Prefix : Wide_String) is
      begin
         for Multiplicity in Id_Multiplicity'Range loop
            declare
               Name : Wide_String := Id_Subtype (Prefix, Opaque, Multiplicity);
               Why_Node_Name : Wide_String := Id_Subtype
                 ("Why_Node", Derived, Multiplicity);
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

   function OCaml_Lower_Identifier (Str : String) return Wide_String;

   function OCaml_Upper_Identifier (Str : String) return Wide_String;

   function Kind_To_String (Kind : Why_Node_Kind) return String;

   ----------------------------
   -- OCaml_Lower_Identifier --
   ----------------------------

   function OCaml_Lower_Identifier (Str : String) return Wide_String is
      Str1 : String := Clean_Identifier (Str);
   begin
      To_Lower (Str1);
      declare
         Str2 : String :=
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
         return To_Wide_String (Str2);
      end;
   end OCaml_Lower_Identifier;

   ----------------------------
   -- OCaml_Upper_Identifier --
   ----------------------------

   function OCaml_Upper_Identifier (Str : String) return Wide_String is
      Str1 : String := Clean_Identifier (Str);
   begin
      To_Lower (Str1);
      if Str1'Length > 0 then
         Str1 (Str1'First) := To_Upper (Str1 (Str1'First));
      end if;
      return To_Wide_String (Str1);
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
         S : Wide_String_Access := String_Lists.Element (Position);
         Name : String := To_String (Strip_Prefix (S.all));
         Type_Tag_Name : Wide_String := OCaml_Lower_Identifier (Name & "_tag");
         Variant_Name : Wide_String := OCaml_Upper_Identifier (Name);
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
         Type_Tag_Name : Wide_String :=
           OCaml_Lower_Identifier
           (To_String (Strip_Prefix (Class.Name.all) & "_tag"));
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
      procedure Print_Subtypes (Prefix : Wide_String);

      -------------------------
      -- Print_Kind_Subtypes --
      -------------------------

      procedure Print_Kind_Subtypes (Position : String_Lists.Cursor) is
         S : constant Wide_String_Access := String_Lists.Element (Position);
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

      procedure Print_Subtypes (Prefix : Wide_String) is
      begin
         for Multiplicity in Id_Multiplicity'Range loop
            declare
               Name : Wide_String := OCaml_Lower_Identifier
                  (To_String
                     (Strip_Prefix
                        (Id_Subtype (Prefix, Derived, Multiplicity))));
               Alias : Wide_String := OCaml_Lower_Identifier
                 (To_String (Id_Subtype ("why_node", Derived, Multiplicity)));
               Type_Tag_Str : Wide_String := OCaml_Lower_Identifier
                 (Strip_Prefix (To_String (Prefix)) & "_tag");
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
         for FI of Common_Fields.Fields loop
            declare
               Field : Wide_String := OCaml_Lower_Identifier
                 (To_String (Strip_Prefix (Field_Name (FI))));
               Typ : Wide_String := OCaml_Lower_Identifier
                 (To_String (Strip_Prefix (Type_Name (FI, Opaque))));
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
               Has_Fields : Boolean :=
                 not Is_Empty (Why_Tree_Info (Kind).Fields);
            begin
               Relative_Indent (O, 4);
               if Has_Fields then
                  P (O, "{");
                  Relative_Indent (O, 2);
                  for FI of Why_Tree_Info (Kind).Fields loop
                     declare
                        Field : Wide_String := OCaml_Lower_Identifier
                          (To_String (Strip_Prefix (Field_Name (FI))));
                        Typ : Wide_String := OCaml_Lower_Identifier
                          (To_String (Strip_Prefix (Type_Name (FI, Derived))));
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
      C : Cursor := First (Fields);
      I : Integer := 1;
   begin
      for I in Res'Range loop
         declare
            Field : Unbounded_String := To_Unbounded_String
              (To_String
                 (OCaml_Lower_Identifier
                    (To_String
                       (Strip_Prefix (Field_Name (Element (C)))))));
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
      C : Cursor := First (Fields);
      I : Integer := 1;
   begin
      for I in Res'Range loop
         declare
            Typ : Unbounded_String := To_Unbounded_String
              (To_String
                 (OCaml_Lower_Identifier
                    (To_String (Strip_Prefix (Type_Name (Element (C), Opaque)))
                       & Suffix)));
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
      Common_Field_Names : Variants :=
        OCaml_Field_Names (Common_Fields.Fields);
      Common_Field_Converters : Variants :=
        OCaml_Field_Types (Common_Fields.Fields, "_from_json");
   begin
      PL (O, "let rec why_node_from_json : 'a why_node from_json = function");
      begin
         Relative_Indent (O, 2);
         for Kind in Why_Tree_Info'Range loop
            declare
               Kind_Str : String := Why_Node_Kind'Image (Kind);
               Info : Why_Node_Info := Why_Tree_Info (Kind);
               Variant_Name : Wide_String :=
                 OCaml_Upper_Identifier
                 (To_String
                    (Strip_Prefix
                       (To_Wide_String
                          (Why_Node_Kind'Image (Kind)))));
               Variant_Field_Names : Variants :=
                 OCaml_Field_Names (Info.Fields);
               Variant_Field_Converters : Variants :=
                 OCaml_Field_Types (Info.Fields, "_from_json");
            begin
               if Kind /= W_Unused_At_Start then
                  --  Pattern matching
                  P (O, "| `List [");
                  P (O, "`String """ & To_Wide_String (Kind_Str) & """");
                  for I in Common_Field_Names'Range loop
                     P (O, "; " & To_Wide_String ((Common_Field_Names (I))));
                  end loop;
                  for I in Variant_Field_Names'Range loop
                     P (O, "; " & To_Wide_String (Variant_Field_Names (I)));
                  end loop;
                  PL (O, "] ->");
                  begin
                     --  Generate variant
                     Relative_Indent (O, 2);
                     PL (O, "let info = {");
                     begin
                        Relative_Indent (O, 2);
                        for I in Common_Field_Names'Range loop
                           P (O, To_Wide_String (Common_Field_Names (I)));
                           P (O, " = ");
                           P (O, To_Wide_String (Common_Field_Converters (I)));
                           P (O, " ");
                           P (O, To_Wide_String (Common_Field_Names (I)));
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
                              P (O, To_Wide_String (Variant_Field_Names (I)));
                              P (O, " = ");
                              P (O, To_Wide_String
                                   (Variant_Field_Converters (I)));
                              P (O, " ");
                              P (O, To_Wide_String (Variant_Field_Names (I)));
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
      procedure Print_Subtypes (Prefix : Wide_String);

      ---------------------------
      -- Process_One_Node_Kind --
      ---------------------------

      procedure Process_One_Node_Kind (Position : String_Lists.Cursor) is
         S : constant Wide_String_Access := String_Lists.Element (Position);
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

      procedure Print_Subtypes (Prefix : Wide_String) is
      begin
         for Multiplicity in Id_Multiplicity'Range loop
            declare
               Prefix_Mult : Wide_String :=
                 Id_Subtype (Prefix, Opaque, Multiplicity);
               Name : Wide_String := OCaml_Lower_Identifier
                 (To_String (Strip_Prefix (Prefix_Mult) & "_from_json"));
               Alias : Wide_String := OCaml_Lower_Identifier
                 (To_String (Id_Subtype ("why_node", Derived, Multiplicity)
                               & "_from_json"));
               Coercion : Wide_String := OCaml_Lower_Identifier
                 (To_String (Strip_Prefix (Prefix) & "_coercion"));
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
         S : Wide_String_Access := String_Lists.Element (Position);
         Name : String := To_String (Strip_Prefix (S.all));
         Coercion : Wide_String :=
           OCaml_Lower_Identifier (Name & "_coercion");
         Res_Type : Wide_String :=
           OCaml_Lower_Identifier (Name & "_tag") & " why_node";
         Variant : Wide_String :=
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
         Coercion : Wide_String := OCaml_Lower_Identifier
           (Strip_Prefix (To_String (Class.Name.all)) & "_coercion");
         Res_Type : Wide_String := OCaml_Lower_Identifier
           (Strip_Prefix (To_String (Class.Name.all)) & "_tag")
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

   procedure Print_OCaml_Enum_From_Json
     (O : in out Output_Record;
      Name : String;
      Vars : Variants);

   --------------------------------
   -- Print_OCaml_Enum_From_Json --
   --------------------------------

   procedure Print_OCaml_Enum_From_Json
     (O : in out Output_Record;
      Name : String;
      Vars : Variants)
   is
      Func_Name : Wide_String :=
        OCaml_Lower_Identifier (Strip_Prefix (Name) & "_from_json");
      Type_Name : Wide_String :=
        OCaml_Lower_Identifier (Strip_Prefix (Name));
   begin
      PL (O, "let " & Func_Name & " : " & Type_Name & " from_json = function");
      begin
         Relative_Indent (O, 2);
         for I in Vars'Range loop
            P (O, "| `Int" & To_Wide_String (Integer'Image (I)));
            PL (O, " -> " & OCaml_Upper_Identifier
                  (Strip_Prefix (To_String (Vars (I)))));
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
     (O : in out Output_Record) is
   begin
      PL (O, "(* Why.Sinfo *)");
      NL (O);
      declare
         EW_Domain_Variants : Variants
           (EW_Domain'Pos (EW_Domain'First) ..
            EW_Domain'Pos (EW_Domain'Last));
      begin
         for I in EW_Domain_Variants'Range loop
            EW_Domain_Variants (I) := To_Unbounded_String
              (EW_Domain'Image (EW_Domain'Val (I)));
         end loop;
         Print_OCaml_Enum_From_Json (O, "EW_Domain", EW_Domain_Variants);
      end;

      declare
         EW_Type_Variants : Variants
           (EW_Type'Pos (EW_Type'First) ..
            EW_Type'Pos (EW_Type'Last));
      begin
         for I in EW_Type_Variants'Range loop
            EW_Type_Variants (I) := To_Unbounded_String
              (EW_Type'Image (EW_Type'Val (I)));
         end loop;
         Print_OCaml_Enum_From_Json (O, "EW_Type", EW_Type_Variants);
      end;

      declare
         EW_Literal_Variants : Variants
           (EW_Literal'Pos (EW_Literal'First) ..
            EW_Literal'Pos (EW_Literal'Last));
      begin
         for I in EW_Literal_Variants'Range loop
            EW_Literal_Variants (I) := To_Unbounded_String
              (EW_Literal'Image (EW_Literal'Val (I)));
         end loop;
         Print_OCaml_Enum_From_Json (O, "EW_Literal", EW_Literal_Variants);
      end;

      declare
         EW_Theory_Type_Variants : Variants
           (EW_Theory_Type'Pos (EW_Theory_Type'First) ..
            EW_Theory_Type'Pos (EW_Theory_Type'Last));
      begin
         for I in EW_Theory_Type_Variants'Range loop
            EW_Theory_Type_Variants (I) := To_Unbounded_String
              (EW_Theory_Type'Image (EW_Theory_Type'Val (I)));
         end loop;
         Print_OCaml_Enum_From_Json
           (O, "EW_Theory_Type", EW_Theory_Type_Variants);
      end;

      declare
         EW_Clone_Type_Variants : Variants
           (EW_Clone_Type'Pos (EW_Clone_Type'First) ..
            EW_Clone_Type'Pos (EW_Clone_Type'Last));
      begin
         for I in EW_Clone_Type_Variants'Range loop
            EW_Clone_Type_Variants (I) := To_Unbounded_String
              (EW_Clone_Type'Image (EW_Clone_Type'Val (I)));
         end loop;
         Print_OCaml_Enum_From_Json
           (O, "EW_Clone_Type", EW_Clone_Type_Variants);
      end;

      declare
         EW_Subst_Type_Variants : Variants
           (EW_Subst_Type'Pos (EW_Subst_Type'First) ..
            EW_Subst_Type'Pos (EW_Subst_Type'Last));
      begin
         for I in EW_Subst_Type_Variants'Range loop
            EW_Subst_Type_Variants (I) := To_Unbounded_String
              (EW_Subst_Type'Image (EW_Subst_Type'Val (I)));
         end loop;
         Print_OCaml_Enum_From_Json
           (O, "EW_Subst_Type", EW_Subst_Type_Variants);
      end;

      declare
         EW_Connector_Variants : Variants
           (EW_Connector'Pos (EW_Connector'First) ..
            EW_Connector'Pos (EW_Connector'Last));
      begin
         for I in EW_Connector_Variants'Range loop
            EW_Connector_Variants (I) := To_Unbounded_String
              (EW_Connector'Image (EW_Connector'Val (I)));
         end loop;
         Print_OCaml_Enum_From_Json
           (O, "EW_Connector", EW_Connector_Variants);
      end;

      declare
         EW_Assert_Kind_Variants : Variants
           (EW_Assert_Kind'Pos (EW_Assert_Kind'First) ..
            EW_Assert_Kind'Pos (EW_Assert_Kind'Last));
      begin
         for I in EW_Assert_Kind_Variants'Range loop
            EW_Assert_Kind_Variants (I) := To_Unbounded_String
              (EW_Assert_Kind'Image (EW_Assert_Kind'Val (I)));
         end loop;
         Print_OCaml_Enum_From_Json
           (O, "EW_Assert_Kind", EW_Assert_Kind_Variants);
      end;
   end Print_OCaml_Why_Sinfo_Types_From_Json;

end Xtree_Why_AST;
