------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

pragma Ada_2005;

with Ada.Command_Line;       use Ada.Command_Line;
with Ada.Containers.Vectors;
with Ada.Strings.Fixed;
with Ada.Strings.Unbounded;  use Ada.Strings.Unbounded;
with Ada.Text_IO;

with DOM.Core.Documents;     use DOM.Core, DOM.Core.Documents;
with DOM.Core.Elements;      use DOM.Core.Elements;
with DOM.Core.Nodes;         use DOM.Core.Nodes;
with DOM.Readers;            use DOM.Readers;
with Input_Sources.File;     use Input_Sources.File;

procedure Tranxgen is

   --  Each field in a protocol message is split in a number of subfields that
   --  never cross byte boundaries.

   type Subfield is record
      Name      : Unbounded_String;
      --  Subfield name

      Shift     : Natural;
      --  Bit count the subfield must be shifted left when constructing the
      --  field's value.

      First_Bit : Natural;
      Last_Bit  : Natural;
      --  Firs and last bit offsets of subfield in message
   end record;

   package Subfield_Vectors is new Ada.Containers.Vectors
     (Element_Type => Subfield, Index_Type => Natural);

   type Field is record
      Name      : Unbounded_String;
      --  Field name

      Length    : Natural;
      --  Total field length in bits

      Subfields : Subfield_Vectors.Vector;
      --  Subfields (always at least one). The First_Bit .. Last_Bit ranges
      --  of successive subfields are contiguous within the message, and the
      --  sum of the lengths of these ranges is Length.
   end record;

   package Field_Vectors is new Ada.Containers.Vectors
     (Element_Type => Field, Index_Type => Natural);

   --  Output context

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
         use Ada.Text_IO;
      begin
         Put (To_String (U.Text));
         if not U.At_BOL then
            New_Line;
         end if;
         New_Line;
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

   --  Utility subprograms

   function Img (N : Integer) return String;
   --  Trimmed image of N

   function First_Element_Child (N : Node) return Node;
   --  Return the first child of N that is an Element_Node

   function Next_Element_Sibling (N : Node) return Node;
   --  Return the next sibling of N that is an Element_Node

   procedure Walk_Siblings
     (N : Node;
      P : access procedure (N : Node));
   --  Apply P to N and each of its (element) siblings

   --  Processing of messages

   type Package_Context is record
      P_Spec    : Output.Unit;
      P_Private : Output.Unit;
      P_Body    : Output.Unit;
   end record;

   procedure Process_Message (Ctx : in out Package_Context; N : Node);
   --  Process a <message> element

   procedure Process_Package (N : Node);
   --  Process a <package> element, generate Ada package spec and body

   Bodies : Unbounded_String;
   Prefix : Unbounded_String;

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

   ---------------------
   -- Process_Message --
   ---------------------

   procedure Process_Message (Ctx : in out Package_Context; N : Node) is
      use Ada.Strings;
      use Ada.Strings.Fixed;

      Message_Name : constant String := Get_Attribute (N, "name");

      Max_Field_Name_Length    : Natural := 0;
      --  Length of longest field name

      Max_Subfield_Name_Length : Natural := 0;
      --  Length of longest subfield name

      Current_Bit_Offset : Natural := 0;

      Fields : Field_Vectors.Vector;

      function Field_Type (F : Field) return String;
      --  Return type name for field F (used in accessors)

      function Subfield_Type (SF : Subfield) return String;
      --  Return type name for subfield SF (used in component declaration)

      procedure Process_Field (N : Node);
      --  Process <field> element

      -------------------
      -- Process_Field --
      -------------------

      procedure Process_Field (N : Node) is
         Field_Name      : constant String := Get_Attribute (N, "name");
         Field_Length    : constant Natural :=
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
         while Remain_Length > 0 loop
            --  Length of next subfield is remaining length, but not going
            --  further than the end of the current byte.

            Subfield_Length :=
              Natural'Min (Remain_Length, 8 - Current_Bit_Offset mod 8);

            Subfield_Name := To_Unbounded_String (Field_Name);

            --  For the case of a field that has multiple subfields, suffix
            --  field name with subfield index.

            if Subfield > 0 or else Subfield_Length < Remain_Length then
               Append (Subfield_Name, "_" & Img (Subfield));
            end if;

            Max_Subfield_Name_Length :=
              Natural'Max (Length (Subfield_Name), Max_Subfield_Name_Length);

            Subfields.Append
              ((Name      => Subfield_Name,
                First_Bit => Current_Bit_Offset,
                Last_Bit  => Current_Bit_Offset + Subfield_Length - 1,
                Shift     => Remain_Length - Subfield_Length));

            Current_Bit_Offset := Current_Bit_Offset + Subfield_Length;
            Remain_Length      := Remain_Length - Subfield_Length;

            Subfield := Subfield + 1;
         end loop;

         Max_Field_Name_Length :=
           Natural'Max (Field_Name'Length, Max_Field_Name_Length);

         Fields.Append
           ((Name      => To_Unbounded_String (Field_Name),
             Length    => Field_Length,
             Subfields => Subfields));
      end Process_Field;

      ----------------
      -- Field_Type --
      ----------------

      function Field_Type (F : Field) return String is
      begin
         return "U" & Img (F.Length) & "_T";
      end Field_Type;

      -------------------
      -- Subfield_Type --
      -------------------

      function Subfield_Type (SF : Subfield) return String is
      begin
         return "U" & Img (SF.Last_Bit - SF.First_Bit + 1) & "_T";
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
      declare
         Hyphens : constant String := (1 .. Message_Name'Length + 6 => '-');
      begin
         PL (Ctx.P_Spec, Hyphens);
         PL (Ctx.P_Spec, "-- " & Message_Name & " --");
         PL (Ctx.P_Spec, Hyphens);
      end;
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
                  SFT     : constant String := Subfield_Type (SF);
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
                  SFT     : constant String := Subfield_Type (SF);
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

         procedure Subfield_Decl (SFC : Subfield_Vectors.Cursor);
         --  Generate component declaration for subfield

         ----------------
         -- Field_Decl --
         ----------------

         procedure Field_Decl (FC : Field_Vectors.Cursor) is
            F : Field renames Field_Vectors.Element (FC);
         begin
            F.Subfields.Iterate (Subfield_Decl'Access);
         end Field_Decl;

         -------------------
         -- Subfield_Decl --
         -------------------

         procedure Subfield_Decl (SFC : Subfield_Vectors.Cursor) is
            SF : Subfield renames Subfield_Vectors.Element (SFC);
         begin
            PL (Ctx.P_Private,
                 Head (To_String (SF.Name), Max_Subfield_Name_Length)
                 & " : " & Subfield_Type (SF)
                 & ";");
         end Subfield_Decl;

      --  Start of processing for Field_Declarations

      begin
         Fields.Iterate (Field_Decl'Access);
      end Field_Declarations;

      DI (Ctx.P_Private);
      PL (Ctx.P_Private, "end record;");

      --  Generate rep clause

      NL (Ctx.P_Private);
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
                      & " .. "    & Img (SF.Last_Bit mod 8) & ";");
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

      procedure Process_Message_In_Package (N : Node);
      --  Call Process_Message for a <message> element in this package

      --------------------------------
      -- Process_Message_In_Package --
      --------------------------------

      procedure Process_Message_In_Package (N : Node) is
      begin
         Process_Message (Ctx, N);
      end Process_Message_In_Package;

   --  Start of processing for Process_Package

   begin
      if Node_Name (N) /= "package" then
         raise Program_Error with "unexpected element: " & Node_Name (N);
      end if;

      PL (Ctx.P_Spec, "pragma Ada_2005;");
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
                                 (Get_Attribute (Import_Node, "use"));
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

      PL (Ctx.P_Private, "private");
      II (Ctx.P_Private);

      PL (Ctx.P_Body, "package body " & Package_Name & " is");
      II (Ctx.P_Body);

      Walk_Siblings
        (First_Element_Child (N), Process_Message_In_Package'Access);

      DI (Ctx.P_Private);
      PL (Ctx.P_Private, "end " & Package_Name & ";");

      DI (Ctx.P_Body);
      PL (Ctx.P_Body, "end " & Package_Name & ";");

      Dump (Ctx.P_Spec);
      Dump (Ctx.P_Private);
      Dump (Ctx.P_Body);
   end Process_Package;

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
end Tranxgen;
