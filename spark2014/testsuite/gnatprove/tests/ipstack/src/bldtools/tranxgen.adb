------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

pragma Ada_2005;

with Ada.Command_Line;       use Ada.Command_Line;
with Ada.Containers.Vectors;
with Ada.Strings.Fixed;
with Ada.Strings.Unbounded;  use Ada.Strings.Unbounded;
with Ada.Text_IO;            use Ada.Text_IO;

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

   function Get_Attribute_With_Default
     (N        : Node;
      Att_Name : String;
      Default  : String) return String;
   --  Return the value of attribute Att_Name of node N, or Default if empty
   --  or missing.

   procedure Process_Message (N : Node);
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

   --------------------------------
   -- Get_Attribute_With_Default --
   --------------------------------

   function Get_Attribute_With_Default
     (N        : Node;
      Att_Name : String;
      Default  : String) return String
   is
      Val : constant String := Get_Attribute (N, Att_Name);
   begin
      if Val = "" then
         return Default;
      else
         return Val;
      end if;
   end Get_Attribute_With_Default;

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

   procedure Process_Message (N : Node) is
      use Ada.Strings;
      use Ada.Strings.Fixed;

      Message_Name : constant String := Get_Attribute (N, "name");

      Ptr_Type : constant String := Get_Attribute_With_Default (N,
                                      Att_Name => "ptrtype",
                                      Default  => "System.Address");

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

      --  Generate record declaration

      Put_Line ("type " & Message_Name & " is record");
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
            Put ("   "
                 & Head (To_String (SF.Name), Max_Subfield_Name_Length)
                 & " : " & Subfield_Type (SF)
                 & ";");
            if SF.Shift > 0 then
               Put (" --  Shift=" & Img (SF.Shift));
            end if;
            New_Line;
         end Subfield_Decl;

      --  Start of processing for Field_Declarations

      begin
         Fields.Iterate (Field_Decl'Access);
      end Field_Declarations;
      Put_Line ("end record;");
      New_Line;

      --  Generate rep clause

      Put_Line ("for " & Message_Name & "'Bit_Order"
                & " use System.High_Order_First;");
      Put_Line ("for " & Message_Name & " use record");

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
            Put_Line ("   "
                      & Head (To_String (SF.Name), Max_Subfield_Name_Length)
                      & " at "    & Img (SF.First_Bit / 8)
                      & " range " & Img (SF.First_Bit mod 8)
                      & " .. "    & Img (SF.Last_Bit mod 8) & ";");
         end Subfield_Rep_Clause;

      --  Start of processing for Representation_Clauses

      begin
         Fields.Iterate (Field_Rep_Clause'Access);
      end Representation_Clauses;

      Put_Line ("end record;");
      New_Line;

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

            procedure BP (S : String);
            --  Append S to body

            procedure BPL (S : String);
            --  Append S and new line to body

            --------
            -- BP --
            --------

            procedure BP (S : String) is
            begin
               Append (Bodies, S);
            end BP;

            ---------
            -- BPL --
            ---------

            procedure BPL (S : String) is
            begin
               BP (S & ASCII.LF);
            end BPL;

         --  Start of processing for Field_Accessors

         begin
            Put_Line (Get_Profile & ";");
            Put_Line (Set_Profile & ";");
            New_Line;

            BPL (Get_Profile & " is");
            BPL ("begin");
            BP  ("   return ");

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
                     BPL ("");
                     BP ("        + ");
                  end if;

                  if Convert then
                     BP (FT & " (");
                  end if;
                  BP ("M." & To_String (SF.Name));
                  if Convert then
                     BP (")");
                  end if;

                  if SF.Shift > 0 then
                     BP (" * 2**" & Img (SF.Shift));
                  end if;

                  First_Subfield := False;
               end Get_Subfield;

            --  Start of processing for Get_Subfields

            begin
               F.Subfields.Iterate (Get_Subfield'Access);
               BPL (";");
            end Get_Subfields;

            BPL ("end " & Field_Name & ";");
            BPL ("");

            --  Setter

            BPL (Set_Profile & " is");
            BPL ("begin");

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
                  BP ("   M." & To_String (SF.Name) & " := ");
                  if Convert then
                     BP (SFT & " (");
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
                  BP (To_String (SF_Expr));

                  if Convert then
                     BP (")");
                  end if;
                  BPL (";");
               end Set_Subfield;

            --  Start of processing for Set_Subfields

            begin
               F.Subfields.Iterate (Set_Subfield'Access);
            end Set_Subfields;

            BPL ("end Set_" & Field_Name & ";");
            BPL ("");
         end Field_Accessors;

      --  Start of processing for Accessors

      begin
         Fields.Iterate (Field_Accessors'Access);
      end Accessors;
   end Process_Message;

   ---------------------
   -- Process_Package --
   ---------------------

   procedure Process_Package (N : Node) is
      Package_Name : constant String := Get_Attribute (N, "name");
   begin
      if Node_Name (N) /= "package" then
         raise Program_Error with "unexpected element: " & Node_Name (N);
      end if;

      Put_Line ("pragma Ada_2005;");
      Put_Line ("with System;");

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
               Put_Line ("with " & Import_Name & ";");
               if Import_Use then
                  Put_Line ("use " & Import_Name & ";");
               end if;
            end;
         end loop;
         Free (Imports);
      end;

      Put_Line ("package " & Package_Name & " is");
      Walk_Siblings (First_Element_Child (N), Process_Message'Access);
      Put_Line ("end " & Package_Name & ";");
      New_Line;

      Put_Line ("package body " & Package_Name & " is");
      Put      (To_String (Bodies));
      Put_Line ("end " & Package_Name & ";");
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
