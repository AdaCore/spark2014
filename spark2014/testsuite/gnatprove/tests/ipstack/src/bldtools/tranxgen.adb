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

   type Subfield is record
      Name      : Unbounded_String;
      Shift     : Natural;
      First_Bit : Natural;
      Last_Bit  : Natural;
   end record;

   package Subfield_Vectors is new Ada.Containers.Vectors
     (Element_Type => Subfield, Index_Type => Natural);

   type Field is record
      Name      : Unbounded_String;
      Length    : Natural;
      Subfields : Subfield_Vectors.Vector;
   end record;

   package Field_Vectors is new Ada.Containers.Vectors
     (Element_Type => Field, Index_Type => Natural);

   function Img (N : Integer) return String is
      use Ada.Strings;
      use Ada.Strings.Fixed;
   begin
      return Trim (N'Img, Both);
   end Img;

   function First_Element_Child (N : Node) return Node;
   function Next_Element_Sibling (N : Node) return Node;

   function First_Element_Child (N : Node) return Node is
      CN : Node := First_Child (N);
   begin
      while CN /= null and then Node_Type (CN) /= Element_Node loop
         CN := Next_Sibling (CN);
      end loop;
      return CN;
   end First_Element_Child;

   function Next_Element_Sibling (N : Node) return Node is
      SN : Node := Next_Sibling (N);
   begin
      while SN /= null and then Node_Type (SN) /= Element_Node loop
         SN := Next_Sibling (SN);
      end loop;
      return SN;
   end Next_Element_Sibling;

   procedure Debug_Node (Msg : String; N : Node);
   procedure Debug_Node (Msg : String; N : Node) is
   begin
      Put_Line (Msg);
      Put_Line ("  Name: " & Node_Name (N));
      Put_Line ("  Type: " & Node_Type (N)'Img);
   end Debug_Node;

   procedure Walk_Siblings
     (N : Node;
      P : access procedure (N : Node));
   --  Apply P to N and each of its siblings

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

   procedure Gen_Message_Decl (N : Node);
   --  Generate type declaration for <message> element

   procedure Gen (N : Node);
   --  Process a <package> element, generate Ada package spec and body

   Bodies : Unbounded_String;

   procedure Gen_Message_Decl (N : Node) is
      use Ada.Strings;
      use Ada.Strings.Fixed;

      Message_Name : constant String := Get_Attribute (N, "name");

      function Get_Ptr_Type return String is
         Ptrtype_Attr : constant String := Get_Attribute (N, "ptrtype");
      begin
         if Ptrtype_Attr = "" then
            return "System.Address";
         else
            return Ptrtype_Attr;
         end if;
      end Get_Ptr_Type;

      Ptr_Type : constant String := Get_Ptr_Type;

      Max_Field_Name_Length    : Natural := 0;
      Max_Subfield_Name_Length : Natural := 0;

      Current_Bit_Offset : Natural := 0;

      Fields : Field_Vectors.Vector;

      procedure Process_Field (N : Node) is
         Field_Name      : constant String := Get_Attribute (N, "name");
         Field_Length    : constant Natural :=
                             Integer'Value (Get_Attribute (N, "length"));
         Remain_Length   : Natural := Field_Length;

         Subfields       : Subfield_Vectors.Vector;

         Subfield        : Natural := 0;
         Subfield_Length : Natural;
         Subfield_Name   : Unbounded_String;

      --  Start of processing for Process_Field

      begin
         while Remain_Length > 0 loop
            Subfield_Length :=
              Natural'Min (Remain_Length, 8 - Current_Bit_Offset mod 8);
            Subfield_Name := To_Unbounded_String (Field_Name);
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
            Remain_Length := Remain_Length - Subfield_Length;
            Subfield := Subfield + 1;
         end loop;

         Max_Field_Name_Length :=
           Natural'Max (Field_Name'Length, Max_Field_Name_Length);
         Fields.Append
           ((Name      => To_Unbounded_String (Field_Name),
             Length    => Field_Length,
             Subfields => Subfields));
      end Process_Field;

      function Field_Type (F : Field) return String is
      begin
         return "U" & Img (F.Length) & "_T";
      end Field_Type;

      function Subfield_Type (SF : Subfield) return String is
      begin
         return "U" & Img (SF.Last_Bit - SF.First_Bit + 1) & "_T";
      end Subfield_Type;

      First_Field : constant Node := First_Element_Child (N);

   begin
      if Node_Name (N) /= "message" then
         return;
      end if;

      Walk_Siblings (First_Field, Process_Field'Access);

      --  Generate record declaration

      Put_Line ("type " & Message_Name & " is record");
      declare
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

         procedure Field_Decl (FC : Field_Vectors.Cursor) is
            F : Field renames Field_Vectors.Element (FC);
         begin
            F.Subfields.Iterate (Subfield_Decl'Access);
         end Field_Decl;
      begin
         Fields.Iterate (Field_Decl'Access);
      end;
      Put_Line ("end record;");
      New_Line;

      --  Generate rep clause

      Put_Line ("for " & Message_Name & "'Bit_Order"
                & " use System.High_Order_First;");
      Put_Line ("for " & Message_Name & " use record");
      declare
         procedure Subfield_Rep_Clause (SFC : Subfield_Vectors.Cursor) is
            SF : Subfield renames Subfield_Vectors.Element (SFC);
         begin
            Put_Line ("   "
                      & Head (To_String (SF.Name), Max_Subfield_Name_Length)
                      & " at "    & Img (SF.First_Bit / 8)
                      & " range " & Img (SF.First_Bit mod 8)
                      & " .. "    & Img (SF.Last_Bit mod 8) & ";");
         end Subfield_Rep_Clause;

         procedure Field_Rep_Clause (FC : Field_Vectors.Cursor) is
            F : Field renames Field_Vectors.Element (FC);
         begin
            F.Subfields.Iterate (Subfield_Rep_Clause'Access);
         end Field_Rep_Clause;
      begin
         Fields.Iterate (Field_Rep_Clause'Access);
      end;

      Put_Line ("end record;");
      New_Line;

      --  Generate accessor declarations and bodies

      declare
         procedure Field_Accessors (FC : Field_Vectors.Cursor) is
            F           : Field renames Field_Vectors.Element (FC);
            FT          : constant String := Field_Type (F);
            Field_Name  : constant String := To_String (F.Name);

            Padded_Name : constant String :=
                            Head (Field_Name, Max_Field_Name_Length);

            Get_Profile : constant String :=
                            "function  " & Padded_Name
                            & "     (MP : " & Ptr_Type & ") return "
                            & Field_Type (F);
            Set_Profile : constant String :=
                            "procedure Set_"
                            & Padded_Name
                            & " (MP : " & Ptr_Type & "; V : "
                            & Field_Type (F) & ")";

            procedure BP (S : String) is
            begin
               Append (Bodies, S);
            end BP;

            procedure BPL (S : String) is
            begin
               BP (S & ASCII.LF);
            end BPL;
         begin
            Put_Line (Get_Profile & ";");
            Put_Line (Set_Profile & ";");
            New_Line;

            BPL (Get_Profile & " is");
            BPL ("   M : " & Message_Name & ";");
            BPL ("   for M'Address use MP;");
            BPL ("   pragma Import (Ada, M);");
            BPL ("begin");
            BP  ("   return ");
            declare
               First_Subfield : Boolean := True;

               procedure Get_Subfield (SFC : Subfield_Vectors.Cursor) is
                  SF      : Subfield renames Subfield_Vectors.Element (SFC);
                  SFT     : constant String := Subfield_Type (SF);
                  Convert : constant Boolean := FT /= SFT;
               begin
                  if not First_Subfield then
                     BPL ("");
                     BP ("      + ");
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
            begin
               F.Subfields.Iterate (Get_Subfield'Access);
               BPL (";");
            end;
            BPL ("end " & Field_Name & ";");
            BPL ("");

            BPL (Set_Profile & " is");
            BPL ("   M : " & Message_Name & ";");
            BPL ("   for M'Address use MP;");
            BPL ("   pragma Import (Ada, M);");
            BPL ("begin");
            declare
               Prev_Shift : Natural := 0;
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
            begin
               F.Subfields.Iterate (Set_Subfield'Access);
            end;
            BPL ("end Set_" & Field_Name & ";");
            BPL ("");
         end Field_Accessors;
      begin
         Fields.Iterate (Field_Accessors'Access);
      end;
   end Gen_Message_Decl;

   procedure Gen (N : Node) is
      Package_Name : constant String := Get_Attribute (N, "name");
   begin
      if Node_Name (N) /= "package" then
         Debug_Node ("Unexpected element in Gen", N);
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
      Walk_Siblings (First_Element_Child (N), Gen_Message_Decl'Access);
      Put_Line ("end " & Package_Name & ";");
      New_Line;

      Put_Line ("package body " & Package_Name & " is");
      Put_Line (To_String (Bodies));
      Put_Line ("end " & Package_Name & ";");
   end Gen;

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

   Gen (Root);

   Free (Read);
   Close (Input);
end Tranxgen;
