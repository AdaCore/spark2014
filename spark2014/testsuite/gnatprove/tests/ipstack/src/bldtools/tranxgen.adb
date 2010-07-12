------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

pragma Ada_2005;

with Ada.Command_Line;       use Ada.Command_Line;
with Ada.containers.Ordered_Sets;
with Ada.Containers.Vectors;
with ada.Exceptions;
with Ada.Strings.Fixed;
with Ada.Strings.Unbounded;  use Ada.Strings.Unbounded;

with GNAT.IO;
with GNAT.OS_Lib;

with DOM.Core.Documents;     use DOM.Core, DOM.Core.Documents;
with DOM.Core.Elements;      use DOM.Core.Elements;
with DOM.Core.Nodes;         use DOM.Core.Nodes;
with DOM.Readers;            use DOM.Readers;
with Input_Sources.File;     use Input_Sources.File;

procedure Tranxgen is

   ------------------------------------
   -- Messages, fields and subfields --
   ------------------------------------

   --  Each numeric field in a protocol message is split in a number of
   --  subfields that never cross byte boundaries.

   type Subfield is record
      Name      : Unbounded_String;
      --  Subfield name

      Shift     : Natural;
      --  Bit count the subfield must be shifted left when constructing the
      --  field's value.

      First_Bit : Natural;
      Length    : Natural;
      --  First bit offset and length of subfield in message
   end record;

   package Subfield_Vectors is new Ada.Containers.Vectors
     (Element_Type => Subfield, Index_Type => Natural);

   type Field_Class_T is (F_Integer, F_Modular, F_Private);
   Default_Field_Class : constant Field_Class_T := F_Integer;

   type Field is record
      Name      : Unbounded_String;
      --  Field name

      Class     : Field_Class_T;
      --  Field type class

      F_Type    : Unbounded_String;
      --  Field type, if specified in source file

      Length    : Natural;
      --  Total field length in bits

      Subfields : Subfield_Vectors.Vector;
      --  Subfields (always at least one). The ranges First_Bit ..
      --  First_Bit + Length- 1 of successive subfields are contiguous within
      --  the message, and the sum of the lengths of these ranges is Length.
   end record;

   package Field_Vectors is new Ada.Containers.Vectors
     (Element_Type => Field, Index_Type => Natural);

   --------------------
   -- Output streams --
   --------------------

   package Output is
      type Unit is limited private;

      Indent_Size : constant := 3;

      procedure P  (U : in out Unit; S : String);
      --  Insert S in U

      procedure PL (U : in out Unit; S : String);
      --  Insert S in U and start new line

      procedure NL (U : in out Unit);
      --  Start new line in U

      procedure II (U : in out Unit);
      --  Increment indentation level

      procedure DI (U : in out Unit);
      --  Decrement indentation level

      procedure Dump (U : Unit);
      --  Display text of unit to standard output

   private
      type Unit is record
         Text   : Unbounded_String;
         Indent : Natural := 0;
         At_BOL : Boolean := True;
      end record;
   end Output;

   ------------
   -- Output --
   ------------

   package body Output is

      --------
      -- DI --
      --------

      procedure DI (U : in out Unit) is
      begin
         U.Indent := U.Indent - 1;
      end DI;

      ----------
      -- Dump --
      ----------

      procedure Dump (U : Unit) is
      begin
         GNAT.IO.Put (To_String (U.Text));
         if not U.At_BOL then
            GNAT.IO.New_Line;
         end if;
      end Dump;

      --------
      -- II --
      --------

      procedure II (U : in out Unit) is
      begin
         U.Indent := U.Indent + 1;
      end II;

      --------
      -- NL --
      --------

      procedure NL (U : in out Unit) is
      begin
         Append (U.Text, ASCII.LF);
         U.At_BOL := True;
      end NL;

      -------
      -- P --
      -------

      procedure P  (U : in out Unit; S : String) is
      begin
         if U.At_BOL then
            Append (U.Text, String'(1 .. U.Indent * Indent_Size => ' '));
            U.At_BOL := False;
         end if;
         Append (U.Text, S);
      end P;

      --------
      -- PL --
      --------

      procedure PL (U : in out Unit; S : String) is
      begin
         P  (U, S);
         NL (U);
      end PL;

   end Output;

   use Output;

   -------------------------
   -- Utility subprograms --
   -------------------------

   function Img (N : Integer) return String;
   --  Trimmed image of N

   procedure Box (U : in out Unit; S : String);
   --  Add box comment with text S to U

   function First_Element_Child (N : Node) return Node;
   --  Return the first child of N that is an Element_Node

   function Next_Element_Sibling (N : Node) return Node;
   --  Return the next sibling of N that is an Element_Node

   procedure Walk_Siblings
     (N : Node;
      P : access procedure (N : Node));
   --  Apply P to N and each of its (element) siblings

   function Subfield_Type_Name (Subfield_Size : Natural) return String;
   --  Return the name of a power-of-two modular type of the given size

   function Get_Attribute
     (N       : Node;
      Name    : String;
      Default : String) return String;
   --  Same as Get_Attribute, but return Default if attribute is missing or
   --  empty.

   -----------------------------------------------------
   -- Processing of XML message format specifications --
   -----------------------------------------------------

   package Natural_Sets is new Ada.Containers.Ordered_Sets (Natural);

   type Package_Context is record
      P_Spec    : Output.Unit;
      P_Private : Output.Unit;
      P_Body    : Output.Unit;

      Subfield_Sizes : Natural_Sets.Set;
   end record;

   procedure Process_Message (Ctx : in out Package_Context; N : Node);
   --  Process a <message> element

   procedure Process_Enum (Ctx : in out Package_Context; N : Node);
   --  Process an <enum> element

   procedure Process_Package (N : Node);
   --  Process a <package> element, generate Ada package spec and body

   Bodies : Unbounded_String;
   Prefix : Unbounded_String;

   ---------
   -- Box --
   ---------

   procedure Box (U : in out Unit; S : String) is
      Hyphens : constant String := (1 .. S'Length + 6 => '-');
   begin
      PL (U, Hyphens);
      PL (U, "-- " & S & " --");
      PL (U, Hyphens);
   end Box;

   -------------------------
   -- First_Element_Child --
   -------------------------

   function First_Element_Child (N : Node) return Node is
      CN : Node := First_Child (N);
   begin
      while CN /= null and then Node_Type (CN) /= Element_Node loop
         CN := Next_Sibling (CN);
      end loop;
      return CN;
   end First_Element_Child;

   -------------------
   -- Get_Attribute --
   -------------------

   function Get_Attribute
     (N       : Node;
      Name    : String;
      Default : String) return String
   is
      Attr : constant String := Get_Attribute (N, Name);
   begin
      if Attr = "" then
         return Default;
      else
         return Attr;
      end if;
   end Get_Attribute;

   ---------
   -- Img --
   ---------

   function Img (N : Integer) return String is
      use Ada.Strings;
      use Ada.Strings.Fixed;
   begin
      return Trim (N'Img, Both);
   end Img;

   --------------------------
   -- Next_Element_Sibling --
   --------------------------

   function Next_Element_Sibling (N : Node) return Node is
      SN : Node := Next_Sibling (N);
   begin
      while SN /= null and then Node_Type (SN) /= Element_Node loop
         SN := Next_Sibling (SN);
      end loop;
      return SN;
   end Next_Element_Sibling;

   ------------------
   -- Process_Enum --
   ------------------

   procedure Process_Enum (Ctx : in out Package_Context; N : Node) is
      Enum_Name : constant String := Get_Attribute (N, "name");
      Prefix    : constant String := Enum_Name & "_";

      Max_Literal_Name_Length : Natural := 0;

      type Literal is record
         Name  : Unbounded_String;
         Value : Natural;
      end record;

      package Literal_Vectors is new Ada.Containers.Vectors
        (Element_Type => Literal, Index_Type => Natural);

      Literals : Literal_Vectors.Vector;

      procedure Process_Literal (N : Node);
      --  Process a <literal> element

      procedure Output_Literal (LC : Literal_Vectors.Cursor);
      --  Generate declaration for literal

      --------------------
      -- Output_Literal --
      --------------------

      procedure Output_Literal (LC : Literal_Vectors.Cursor) is
         use Ada.Strings.Fixed;
         L : Literal renames Literal_Vectors.Element (LC);
      begin
         PL (Ctx.P_Spec, Prefix
                           & Head (To_String (L.Name), Max_Literal_Name_Length)
                           & " : constant := " & Img (L.Value) & ";");
      end Output_Literal;

      ---------------------
      -- Process_Literal --
      ---------------------

      procedure Process_Literal (N : Node) is
         Name  : constant String := Get_Attribute (N, "name");
         Value : constant Natural :=
                   Natural'Value (Get_Attribute (N, "value"));
      begin
         Max_Literal_Name_Length :=
           Natural'Max (Name'Length, Max_Literal_Name_Length);
         Literals.Append ((To_Unbounded_String (Name), Value));
      end Process_Literal;

   --  Start of processing for Process_Enum

   begin
      Walk_Siblings (First_Element_Child (N), Process_Literal'Access);

      NL (Ctx.P_Spec);
      Box (Ctx.P_Spec, Enum_Name);
      NL (Ctx.P_Spec);

      Literals.Iterate (Output_Literal'Access);
   end Process_Enum;

   ---------------------
   -- Process_Message --
   ---------------------

   procedure Process_Message (Ctx : in out Package_Context; N : Node) is
      use Ada.Strings;
      use Ada.Strings.Fixed;

      Message_Name : constant String := Get_Attribute (N, "name");

      Alignment : Natural := 0;
      --  Alignment is by default the size of the largest field that itself
      --  is so aligned.

      Max_Field_Name_Length    : Natural := 0;
      --  Length of longest field name

      Max_Subfield_Name_Length : Natural := 0;
      --  Length of longest subfield name

      Current_Bit_Offset : Natural := 0;

      Fields : Field_Vectors.Vector;

      function Field_Type (F : Field) return String;
      --  Return type name for field F (used in accessors)

      function Subfield_Type (F : Field; SF : Subfield) return String;
      --  Return type name for subfield SF in F (used in component declaration)

      procedure Process_Field (N : Node);
      --  Process <field> element

      -------------------
      -- Process_Field --
      -------------------

      procedure Process_Field (N : Node) is
         Field_Name       : constant String := Get_Attribute (N, "name");
         Field_Class_Attr : constant String := Get_Attribute (N, "class");
         Field_Class      : Field_Class_T;
         Field_Length     : constant Natural :=
                              Integer'Value (Get_Attribute (N, "length"));

         Remain_Length   : Natural := Field_Length;
         --  Count of bits to be assigned to further subfields

         Subfields       : Subfield_Vectors.Vector;

         Subfield        : Natural := 0;
         --  Index of current subfield

         Subfield_Length : Natural;
         --  Length of current subfield

         Subfield_Name   : Unbounded_String;
         --  Name of current subfield

      --  Start of processing for Process_Field

      begin
         if Field_Class_Attr = "" then
            Field_Class := Default_Field_Class;
         else
            Field_Class := Field_Class_T'Value ("F_" & Field_Class_Attr);
         end if;

         while Remain_Length > 0 loop
            --  For numeric (integer or modular) fields, length of next
            --  subfield is remaining length, but not going further than the
            --  end of the current byte. For private fields, map as a whole.

            if Field_Class = F_Private then
               Subfield_Length := Field_Length;

            else
               Subfield_Length :=
                 Natural'Min (Remain_Length, 8 - Current_Bit_Offset mod 8);
            end if;

            Subfield_Name := To_Unbounded_String (Field_Name);

            --  For the case of a field that has multiple subfields, suffix
            --  field name with subfield index, and ensure we generate an
            --  appropriate internal subfield type.

            if Subfield > 0 or else Subfield_Length < Remain_Length then
               Append (Subfield_Name, "_" & Img (Subfield));
               Ctx.Subfield_Sizes.Include (Subfield_Length);
            end if;

            Max_Subfield_Name_Length :=
              Natural'Max (Length (Subfield_Name), Max_Subfield_Name_Length);

            Subfields.Append
              ((Name      => Subfield_Name,
                First_Bit => Current_Bit_Offset,
                Length    => Subfield_Length,
                Shift     => Remain_Length - Subfield_Length));

            Current_Bit_Offset := Current_Bit_Offset + Subfield_Length;
            Remain_Length      := Remain_Length - Subfield_Length;

            Subfield := Subfield + 1;
         end loop;

         Max_Field_Name_Length :=
           Natural'Max (Field_Name'Length, Max_Field_Name_Length);

         Fields.Append
           ((Name      => To_Unbounded_String (Field_Name),
             Class     => Field_Class,
             F_Type    => To_Unbounded_String (Get_Attribute (N, "type")),
             Length    => Field_Length,
             Subfields => Subfields));

         if Current_Bit_Offset mod Field_Length = 0 then
            Alignment := Natural'Max (Field_Length, Alignment);
         end if;
      end Process_Field;

      ----------------
      -- Field_Type --
      ----------------

      function Field_Type (F : Field) return String is
      begin
         case F.Class is
            when F_Integer =>
               return "U" & Img (F.Length) & "_T";

            when F_Modular =>
               return "M" & Img (F.Length) & "_T";

            when F_Private =>
               return To_String (F.F_Type);
         end case;
      end Field_Type;

      -------------------
      -- Subfield_Type --
      -------------------

      function Subfield_Type (F : Field; SF : Subfield) return String is
         use type Ada.Containers.Count_Type;
      begin
         if F.Subfields.Length = 1 then
            return Field_Type (F);

         else
            pragma Assert (F.Class /= F_Private);
            return Subfield_Type_Name (SF.Length);
         end if;
      end Subfield_Type;

      First_Field : constant Node := First_Element_Child (N);

   --  Start of processing for Process_Message

   begin
      if Node_Name (N) /= "message" then
         return;
      end if;

      Prefix := To_Unbounded_String (Get_Attribute (N, "prefix"));

      Walk_Siblings (First_Field, Process_Field'Access);

      --  Generate private type declaration

      NL (Ctx.P_Spec);
      Box (Ctx.P_Spec, Message_Name);

      NL (Ctx.P_Spec);
      PL (Ctx.P_Spec, "type " & Message_Name & " is private;");

      --  Generate accessor declarations and bodies

      Accessors : declare
         procedure Field_Accessors (FC : Field_Vectors.Cursor) is
            F           : Field renames Field_Vectors.Element (FC);
            FT          : constant String := Field_Type (F);
            Field_Name  : constant String := To_String (Prefix & F.Name);

            Padded_Name : constant String :=
                            Head (Field_Name,
                                  Length (Prefix) + Max_Field_Name_Length);

            Get_Profile : constant String :=
                            "function  " & Padded_Name
                            & "     (M : " & Message_Name & ") return "
                            & Field_Type (F);

            Set_Profile : constant String :=
                            "procedure Set_"
                            & Padded_Name
                            & " (M : in out " & Message_Name & "; V : "
                            & Field_Type (F) & ")";

         --  Start of processing for Field_Accessors

         begin
            NL (Ctx.P_Spec);
            PL (Ctx.P_Spec, Get_Profile & ";");
            PL (Ctx.P_Spec, Set_Profile & ";");

            NL (Ctx.P_Body);
            PL (Ctx.P_Body, Get_Profile & " is");
            PL (Ctx.P_Body, "begin");
            II (Ctx.P_Body);
            P  (Ctx.P_Body, "return ");

            Get_Subfields : declare
               First_Subfield : Boolean := True;
               --  Set True for the first subfield only

               procedure Get_Subfield (SFC : Subfield_Vectors.Cursor);
               --  Generate subexpression for subfield

               procedure Get_Subfield (SFC : Subfield_Vectors.Cursor) is
                  SF      : Subfield renames Subfield_Vectors.Element (SFC);
                  SFT     : constant String := Subfield_Type (F, SF);
                  Convert : constant Boolean := FT /= SFT;
               begin
                  if not First_Subfield then
                     NL (Ctx.P_Body);
                     P  (Ctx.P_Body, "     + ");
                  end if;

                  if Convert then
                     P  (Ctx.P_Body, FT & " (");
                  end if;
                  P  (Ctx.P_Body, "M." & To_String (SF.Name));
                  if Convert then
                     P  (Ctx.P_Body, ")");
                  end if;

                  if SF.Shift > 0 then
                     P  (Ctx.P_Body, " * 2**" & Img (SF.Shift));
                  end if;

                  First_Subfield := False;
               end Get_Subfield;

            --  Start of processing for Get_Subfields

            begin
               F.Subfields.Iterate (Get_Subfield'Access);
               PL (Ctx.P_Body, ";");
            end Get_Subfields;

            DI (Ctx.P_Body);
            PL (Ctx.P_Body, "end " & Field_Name & ";");

            --  Setter

            NL (Ctx.P_Body);
            PL (Ctx.P_Body, Set_Profile & " is");
            PL (Ctx.P_Body, "begin");
            II (Ctx.P_Body);

            Set_Subfields : declare
               Prev_Shift : Natural := 0;
               --  Shift amount of previous subfield

               procedure Set_Subfield (SFC : Subfield_Vectors.Cursor);
               --  Generate assignment to subfield

               ------------------
               -- Set_Subfield --
               ------------------

               procedure Set_Subfield (SFC : Subfield_Vectors.Cursor) is
                  SF      : Subfield renames Subfield_Vectors.Element (SFC);
                  SFT     : constant String := Subfield_Type (F, SF);
                  Convert : constant Boolean := FT /= SFT;

                  SF_Expr : Unbounded_String;

               begin
                  P  (Ctx.P_Body, "M." & To_String (SF.Name) & " := ");
                  if Convert then
                     P  (Ctx.P_Body, SFT & " (");
                  end if;

                  SF_Expr := To_Unbounded_String ("V");
                  if SF.Shift > 0 then
                     Append (SF_Expr, " / 2**" & Img (SF.Shift));
                  end if;
                  if Prev_Shift > 0 then
                     if SF.Shift > 0 then
                        SF_Expr := "(" & SF_Expr & ")";
                     end if;
                     SF_Expr := SF_Expr & " mod 2**"
                                  & Img (Prev_Shift - SF.Shift);
                  end if;
                  Prev_Shift := SF.Shift;
                  P  (Ctx.P_Body, To_String (SF_Expr));

                  if Convert then
                     P  (Ctx.P_Body, ")");
                  end if;
                  PL (Ctx.P_Body, ";");
               end Set_Subfield;

            --  Start of processing for Set_Subfields

            begin
               F.Subfields.Iterate (Set_Subfield'Access);
            end Set_Subfields;

            DI (Ctx.P_Body);
            PL (Ctx.P_Body, "end Set_" & Field_Name & ";");

         end Field_Accessors;

      --  Start of processing for Accessors

      begin
         Fields.Iterate (Field_Accessors'Access);
      end Accessors;

      --  Generate record declaration

      NL (Ctx.P_Private);
      PL (Ctx.P_Private, "type " & Message_Name & " is record");
      II (Ctx.P_Private);
      Field_Declarations : declare
         procedure Field_Decl (FC : Field_Vectors.Cursor);
         --  Generate component declarations for all subfields of field

         ----------------
         -- Field_Decl --
         ----------------

         procedure Field_Decl (FC : Field_Vectors.Cursor) is
            F : Field renames Field_Vectors.Element (FC);

            procedure Subfield_Decl (SFC : Subfield_Vectors.Cursor);
            --  Generate component declaration for subfield

            -------------------
            -- Subfield_Decl --
            -------------------

            procedure Subfield_Decl (SFC : Subfield_Vectors.Cursor) is
               SF : Subfield renames Subfield_Vectors.Element (SFC);
            begin
               PL (Ctx.P_Private,
                   Head (To_String (SF.Name), Max_Subfield_Name_Length)
                   & " : " & Subfield_Type (F, SF)
                   & ";");
            end Subfield_Decl;

         --  Start of processing for Field_Decl

         begin
            F.Subfields.Iterate (Subfield_Decl'Access);
         end Field_Decl;

      --  Start of processing for Field_Declarations

      begin
         Fields.Iterate (Field_Decl'Access);
      end Field_Declarations;

      DI (Ctx.P_Private);
      PL (Ctx.P_Private, "end record;");

      --  Generate rep clause

      NL (Ctx.P_Private);
      PL (Ctx.P_Private, "for " & Message_Name & "'Alignment use "
                           & Img (Alignment / 8) & ";");
      PL (Ctx.P_Private, "for " & Message_Name & "'Bit_Order"
                    & " use System.High_Order_First;");
      PL (Ctx.P_Private, "for " & Message_Name & " use record");
      II (Ctx.P_Private);

      Representation_Clauses : declare
         procedure Field_Rep_Clause (FC : Field_Vectors.Cursor);
         --  Generate representation clauses for all subfields of field

         procedure Subfield_Rep_Clause (SFC : Subfield_Vectors.Cursor);
         --  Generate representation clause for subfield

         ----------------------
         -- Field_Rep_Clause --
         ----------------------

         procedure Field_Rep_Clause (FC : Field_Vectors.Cursor) is
            F : Field renames Field_Vectors.Element (FC);
         begin
            F.Subfields.Iterate (Subfield_Rep_Clause'Access);
         end Field_Rep_Clause;

         -------------------------
         -- Subfield_Rep_Clause --
         -------------------------

         procedure Subfield_Rep_Clause (SFC : Subfield_Vectors.Cursor) is
            SF : Subfield renames Subfield_Vectors.Element (SFC);
         begin
            PL (Ctx.P_Private,
                      Head (To_String (SF.Name), Max_Subfield_Name_Length)
                      & " at "    & Img (SF.First_Bit / 8)
                      & " range " & Img (SF.First_Bit mod 8)
                      & " .. "    & Img (SF.First_Bit mod 8 + SF.Length - 1)
                      & ";");
         end Subfield_Rep_Clause;

      --  Start of processing for Representation_Clauses

      begin
         Fields.Iterate (Field_Rep_Clause'Access);
      end Representation_Clauses;

      DI (Ctx.P_Private);
      PL (Ctx.P_Private, "end record;");

   end Process_Message;

   ---------------------
   -- Process_Package --
   ---------------------

   procedure Process_Package (N : Node) is
      Package_Name : constant String := Get_Attribute (N, "name");
      Ctx : Package_Context;

      procedure Process_Child (N : Node);
      --  Call Process_<element>

      procedure Prelude (U : in out Unit);
      --  Output standard text at the top of evert unit

      -------------
      -- Prelude --
      -------------

      procedure Prelude (U : in out Unit) is
      begin
         PL (U, "--  This file has been automatically generated from "
             & Argument (1));
         PL (U, "--  DO NOT EDIT!!!");
         NL (U);
         PL (U, "pragma Warnings (Off);");
         PL (U, "pragma Style_Checks (""NM32766"");");
         PL (U, "pragma Ada_2005;");
         NL (U);
      end Prelude;

      -------------------
      -- Process_Child --
      -------------------

      procedure Process_Child (N : Node) is
      begin
         if Node_Name (N) = "message" then
            Process_Message (Ctx, N);

         elsif Node_Name (N) = "enum" then
            Process_Enum (Ctx, N);

         else
            return;
         end if;
      end Process_Child;

   --  Start of processing for Process_Package

   begin
      if Node_Name (N) /= "package" then
         raise Program_Error with "unexpected element: " & Node_Name (N);
      end if;

      Prelude (Ctx.P_Spec);
      Prelude (Ctx.P_Body);

      PL (Ctx.P_Spec, "with System;");

      declare
         Imports : Node_List :=
                     Elements.Get_Elements_By_Tag_Name (N, "import");
      begin
         for J in 0 .. Length (Imports) - 1 loop
            declare
               Import_Node : constant Node := Item (Imports, J);
               Import_Name : constant String :=
                               Get_Attribute (Import_Node, "name");
               Import_Use  : constant Boolean :=
                               Boolean'Value
                                 (Get_Attribute (Import_Node,
                                    Name    => "use",
                                    Default => "FALSE"));
            begin
               PL (Ctx.P_Spec, "with " & Import_Name & ";");
               if Import_Use then
                  PL (Ctx.P_Spec, "use " & Import_Name & ";");
               end if;
            end;
         end loop;
         Free (Imports);
      end;

      NL (Ctx.P_Spec);
      PL (Ctx.P_Spec, "package " & Package_Name & " is");
      II (Ctx.P_Spec);

      II (Ctx.P_Private);

      PL (Ctx.P_Body, "package body " & Package_Name & " is");
      II (Ctx.P_Body);

      Walk_Siblings
        (First_Element_Child (N), Process_Child'Access);

      DI (Ctx.P_Private);
      PL (Ctx.P_Private, "end " & Package_Name & ";");

      DI (Ctx.P_Body);
      PL (Ctx.P_Body, "end " & Package_Name & ";");

      --  Generate declarations for subfield types

      NL (Ctx.P_Spec);
      DI (Ctx.P_Spec);
      PL (Ctx.P_Spec, "private");
      II (Ctx.P_Spec);

      Subfield_Types : declare
         procedure Declare_Subfield_Type (SFTC : Natural_Sets.Cursor);
         --  Declare modular type for subfield size denoted by SFTC

         ---------------------------
         -- Declare_Subfield_Type --
         ---------------------------

         procedure Declare_Subfield_Type (SFTC : Natural_Sets.Cursor)  is
            Subfield_Size : Natural renames Natural_Sets.Element (SFTC);
         begin
            PL (Ctx.P_Spec, "type " & Subfield_Type_Name (Subfield_Size)
                & " is mod 2**"  & Img (Subfield_Size) & ";");
         end Declare_Subfield_Type;

      begin
         Ctx.Subfield_Sizes.Iterate (Declare_Subfield_Type'Access);
      end Subfield_Types;

      Dump (Ctx.P_Spec);
      Dump (Ctx.P_Private);
      Dump (Ctx.P_Body);
   end Process_Package;

   ------------------------
   -- Subfield_Type_Name --
   ------------------------

   function Subfield_Type_Name (Subfield_Size : Natural) return String is
   begin
      return "Bits_" & Img (Subfield_Size);
   end Subfield_Type_Name;

   -------------------
   -- Walk_Siblings --
   -------------------

   procedure Walk_Siblings
     (N : Node;
      P : access procedure (N : Node))
   is
      NN : Node := N;
   begin
      while NN /= null loop
         P (NN);
         NN := Next_Element_Sibling (NN);
      end loop;
   end Walk_Siblings;

   Input : File_Input;
   Read  : DOM.Readers.Tree_Reader;
   Doc   : Document;
   Root  : DOM.Core.Element;

--  Start of processing for Tranxgen

begin
   Open (Argument (1), Input);
   Parse (Read, Input);

   Doc  := Get_Tree (Read);
   Root := Get_Element (Doc);

   Process_Package (Root);

   Free (Read);
   Close (Input);

exception

   when E : others =>
      GNAT.IO.Put_Line
        ("Exception raised: " & Ada.Exceptions.Exception_Information (E));
      GNAT.OS_Lib.OS_Exit (1);
end Tranxgen;
