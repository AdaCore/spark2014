------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

pragma Ada_2005;

with Ada.Command_Line;       use Ada.Command_Line;
with Ada.Strings.Fixed;
with Ada.Strings.Unbounded;  use Ada.Strings.Unbounded;
with Ada.Text_IO;            use Ada.Text_IO;

with DOM.Core.Documents;     use DOM.Core, DOM.Core.Documents;
with DOM.Core.Elements;      use DOM.Core.Elements;
with DOM.Core.Nodes;         use DOM.Core.Nodes;
with DOM.Readers;            use DOM.Readers;
with Input_Sources.File;     use Input_Sources.File;

procedure Tranxgen is

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

   procedure Gen_Message_Decl (N : Node) is
      use Ada.Strings;
      use Ada.Strings.Fixed;

      Message_Name : constant String := Get_Attribute (N, "name");
      Max_Field_Name_Length : Natural := 0;

      function Get_Word_Size return Natural is
         WS : constant String := Get_Attribute (N, "wordsize");
      begin
         if WS = "" then
            return 8;
         else
            return Natural'Value (WS);
         end if;
      end Get_Word_Size;

      Word_Size : constant Natural := Get_Word_Size;
      Word_Units : constant Natural := Word_Size / 8;
      Current_Bit_Offset : Natural := 0;

      procedure Update_Max_Field_Name_Length (N : Node) is
         Name : constant String  := Get_Attribute (N, "name");
         L    : constant Natural := Name'Length;
      begin
         if L > Max_Field_Name_Length then
            Max_Field_Name_Length := L;
         end if;
      end Update_Max_Field_Name_Length;

      procedure Gen_Field_Decl (N : Node) is
         Field_Name   : constant String := Get_Attribute (N, "name");
         Field_Length : constant Integer :=
                          Integer'Value (Get_Attribute (N, "length"));
         Field_Type   : constant String :=
                          "U" & Img (Field_Length) & "_T";
      begin
         Put_Line ("   " & Head (Field_Name, Max_Field_Name_Length) & " : "
                         & Field_Type & ";");
      end Gen_Field_Decl;

      procedure Gen_Field_Rep_Clause (N : Node) is
         use Ada.Strings.Fixed;
         Field_Name   : constant String := Get_Attribute (N, "name");
         Field_Length : constant Integer :=
                           Integer'Value (Get_Attribute (N, "length"));

         Word_Offset  : constant Natural := Current_Bit_Offset / Word_Size;

         Bit_Range_Lo : constant Natural := Current_Bit_Offset mod Word_Size;
         Bit_Range_Hi : constant Natural := Bit_Range_Lo + Field_Length - 1;
         pragma Assert (Bit_Range_Hi < Word_Size);
         Bit_Range    : constant array (Boolean) of Natural :=
                          (False => Bit_Range_Hi, True => Bit_Range_Lo);

         Field_Position : constant String :=
                            Img (Word_Offset) & "*" & Img (Word_Units);

         function Bit_Bound (Low : Boolean) return String is
         begin
            if True then
               return "BE*" & Img (Bit_Range (Low)) &
                   " + LE*" & Img (Word_Size - 1 - Bit_Range (not Low));
            else
               return Img (Bit_Range (Low));
            end if;
         end Bit_Bound;

         Field_Range  : constant String :=
                          Bit_Bound (Low => True)
                            & " .. " &
                          Bit_Bound (Low => False);
      begin
         Put_Line ("   " & Head (Field_Name, Max_Field_Name_Length)
                   & " at " & Field_Position
                   & " range " & Field_Range & ";");
         Current_Bit_Offset := Current_Bit_Offset + Field_Length;
      end Gen_Field_Rep_Clause;

      First_Field : constant Node := First_Element_Child (N);

   begin
      if Node_Name (N) /= "message" then
         return;
      end if;

      Walk_Siblings (First_Field, Update_Max_Field_Name_Length'Access);
      Put_Line ("type " & Message_Name & " is record");
      Walk_Siblings (First_Field, Gen_Field_Decl'Access);
      Put_Line ("end record;");

      New_Line;

      Put_Line ("for " & Message_Name & "'Bit_Order"
                & " use System.High_Order_First;");
      Put_Line ("for " & Message_Name & " use record");
      Walk_Siblings (First_Field, Gen_Field_Rep_Clause'Access);
      Put_Line ("end record;");
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
      Put_Line ("use type System.Bit_Order;");
      Put_Line ("LE : constant := Boolean'Pos (System.Default_Bit_Order"
                                         & " = System.Low_Order_First);");
      Put_Line ("BE : constant := 1 - LE;");

      Walk_Siblings (First_Element_Child (N), Gen_Message_Decl'Access);
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
