------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--           Copyright (C) 2010-2014, Free Software Foundation, Inc.        --
------------------------------------------------------------------------------

pragma Ada_2012;

with Ada.containers.Ordered_Sets;
with Ada.Containers.Vectors;
with Ada.Directories;        use Ada.Directories;
with Ada.Exceptions;
with Ada.Streams.Stream_IO;
with Ada.Strings.Fixed;
with Ada.Strings.Unbounded;  use Ada.Strings.Unbounded;
with Ada.Text_IO;            use Ada.Text_IO;

with GNAT.Command_Line;      use GNAT.Command_Line;
with GNAT.OS_Lib;            use GNAT.OS_Lib;

with DOM.Core.Documents;     use DOM.Core, DOM.Core.Documents;
with DOM.Core.Elements;      use DOM.Core.Elements;
with DOM.Core.Nodes;         use DOM.Core.Nodes;
with DOM.Readers;            use DOM.Readers;
with Input_Sources.File;     use Input_Sources.File;

procedure Tranxgen is

   use Ada.Strings;
   use Ada.Strings.Fixed;

   use type Ada.Containers.Count_Type;

   procedure Usage;
   --  Display usage information and exit

   ------------------------------------
   -- Messages, fields and subfields --
   ------------------------------------

   type Field_Class_T is (F_Integer, F_Modular, F_Private);
   Default_Field_Class : constant Field_Class_T := F_Integer;

   type Field is record
      Name      : Unbounded_String;
      --  Field name

      Class     : Field_Class_T;
      --  Field type class

      F_Type    : Unbounded_String;
      --  Field type, if specified in source file

      First_Bit : Natural;
      Length    : Natural;
      --  Bit offset and total bit length

      Export : Boolean;
      --  True if C accessors should be generated
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

      procedure Dump (U : Unit; F : Ada.Streams.Stream_IO.File_Type);
      --  Display text of unit U to F

   private
      type Unit is record
         Text   : Unbounded_String;
         Indent : Natural := 0;
         At_BOL : Boolean := True;
      end record;
   end Output;

   Input_Name    : GNAT.OS_Lib.String_Access;
   --  Name of input file

   Output_Dir    : GNAT.OS_Lib.String_Access;
   --  Output directory

   Output_Prefix : GNAT.OS_Lib.String_Access;
   --  Prefix for output file names (includes Output_Dir)

   Export_Prefix : GNAT.OS_Lib.String_Access;
   --  If not null, all message accessors are exported with the given prefix

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

      procedure Dump (U : Unit; F : Ada.Streams.Stream_IO.File_Type) is
      begin
         declare
            use Ada.Streams, Ada.Streams.Stream_IO;

            Contents     : constant String := To_String (U.Text);
            Contents_SEA : Stream_Element_Array (1 .. Contents'Length);
            for Contents_SEA'Address use Contents'Address;
            pragma Import (Ada, Contents_SEA);
         begin
            Write (F, Contents_SEA);
            if not U.At_BOL then
               Write (F, Stream_Element_Array'(1 => Character'Pos (ASCII.LF)));
            end if;
         end;
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

   type Lang is (Lang_Ada, Lang_C);
   function Img
     (N    : Integer;
      Base : Integer := 10;
      L    : Lang := Lang_Ada) return String;
   --  Trimmed image of N in L's syntax

   procedure Box (U : in out Unit; S : String; L : Lang := Lang_Ada);
   --  Add box comment with text S to U

   function First_Element_Child (N : Node) return Node;
   --  Return the first child of N that is an Element_Node

   function Next_Element_Sibling (N : Node) return Node;
   --  Return the next sibling of N that is an Element_Node

   procedure Walk_Siblings
     (N : Node;
      P : access procedure (N : Node));
   --  Apply P to N and each of its (element) siblings

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
      --  Ada source

      P_C       : Output.Unit;
      --  C binding

      Types_Unit : Unbounded_String;
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

   procedure Box (U : in out Unit; S : String; L : Lang := Lang_Ada) is
   begin
      case L is
         when Lang_Ada =>
            declare
               Hyphens : constant String := (1 .. S'Length + 6 => '-');
            begin
               PL (U, Hyphens);
               PL (U, "-- " & S & " --");
               PL (U, Hyphens);
            end;

         when Lang_C =>
            declare
               Stars : constant String := (1 .. S'Length + 6 => '*');
            begin
               PL (U, "/" & Stars);
               PL (U, " ** " & S & " **");
               PL (U, " " & Stars & "/");
            end;
      end case;
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

   function Img
     (N    : Integer;
      Base : Integer := 10;
      L    : Lang := Lang_Ada) return String
   is
      NN : Integer := N;
      Digit  : constant array (0 .. 15) of Character := "0123456789abcdef";
      Result : Unbounded_String;
   begin
      if Base < 2 or else Base > 16 then
         raise Constraint_Error;
      end if;

      loop
         Result := Digit (NN mod base) & Result;
         NN := NN / Base;
         exit when NN = 0;
      end loop;

      if Base /= 10 then
         if L = Lang_Ada then
            Result := Trim (Integer'Image (Base), Both) & "#" & Result & "#";
         else
            case Base is
               when 8 =>
                  Result := "0" & Result;
               when 16 =>
                  Result := "0x" & Result;
               when others =>
                  raise Program_Error with
                    "base" & Base'Img & " not supported for "
                      & L'Img & " output";
            end case;
         end if;
      end if;
      return To_String (Result);
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
         Value : Integer;
         Base  : Natural;
      end record;

      package Literal_Vectors is new Ada.Containers.Vectors
        (Element_Type => Literal, Index_Type => Natural);

      Literals : Literal_Vectors.Vector;

      procedure Process_Literal (N : Node);
      --  Process a <literal> element

      ---------------------
      -- Process_Literal --
      ---------------------

      procedure Process_Literal (N : Node) is
         Name  : constant String := Get_Attribute (N, "name");
         Image : constant String := Trim (Get_Attribute (N, "value"), Both);
         Value : constant Integer := Integer'Value (Image);
         Base  : Natural;
      begin
         Max_Literal_Name_Length :=
           Natural'Max (Name'Length, Max_Literal_Name_Length);

         Base := 10;

         Find_Base : for J in Image'Range loop
            if Image (J) = '#' then
               Base := Integer'Value (Image (Image'First .. J - 1));
               exit Find_Base;
            end if;
         end loop Find_Base;

         Literals.Append
           ((Name  => To_Unbounded_String (Name),
             Value => Value,
             Base  => Base));
      end Process_Literal;

   --  Start of processing for Process_Enum

   begin
      Walk_Siblings (First_Element_Child (N), Process_Literal'Access);

      NL  (Ctx.P_Spec);
      Box (Ctx.P_Spec, Enum_Name);
      NL  (Ctx.P_Spec);

      if Export_Prefix /= null then
         NL  (Ctx.P_C);
         Box (Ctx.P_C, Enum_Name, Lang_C);
         NL  (Ctx.P_C);
      end if;

      for L of Literals loop
         declare
            L_Name : constant String :=
                       Prefix &
                         Head (To_String (L.Name), Max_Literal_Name_Length);
         begin
            PL (Ctx.P_Spec, L_Name
                              & " : constant := "
                              & Img (L.Value, Base => L.Base) & ";");

            if Export_Prefix /= null then
               PL (Ctx.P_C, "#define " & L_Name
                   & " " & Img (L.Value, Base => L.Base, L => Lang_C));
            end if;
         end;
      end loop;
   end Process_Enum;

   ---------------------
   -- Process_Message --
   ---------------------

   procedure Process_Message (Ctx : in out Package_Context; N : Node) is
      Message_Name : constant String := Get_Attribute (N, "name");

      Max_Field_Name_Length    : Natural := 0;
      --  Length of longest field name

      Current_Bit_Offset : Natural := 0;

      Fields : Field_Vectors.Vector;

      function Field_Type (F : Field; L : Lang := Lang_Ada) return String;
      --  Return type name for field F (used in accessors)

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

      begin
         if Field_Class_Attr = "" then
            Field_Class := Default_Field_Class;
         else
            Field_Class := Field_Class_T'Value ("F_" & Field_Class_Attr);
         end if;

         if Field_Class = F_Private
              and then
            Current_Bit_Offset mod 8 /= 0
         then
            raise Constraint_Error with
              "private field spanning multiple bytes must be byte aligned";
         end if;

         Max_Field_Name_Length :=
           Natural'Max (Field_Name'Length, Max_Field_Name_Length);

         Fields.Append
           ((Name      => To_Unbounded_String (Field_Name),
             Class     => Field_Class,
             F_Type    => To_Unbounded_String (Get_Attribute (N, "type")),
             First_Bit => Current_Bit_Offset,
             Length    => Field_Length,
             Export    => Field_Length <= 32));
         Current_Bit_Offset := Current_Bit_Offset + Field_Length;
      end Process_Field;

      ----------------
      -- Field_Type --
      ----------------

      function Field_Type (F : Field; L : Lang := Lang_Ada) return String
      is
         Prefix : Unbounded_String;
      begin
         if L = Lang_Ada then
            Prefix := Ctx.Types_Unit;
         end if;

         if Length (Prefix) > 0 then
            Append (Prefix, ".");
         end if;
         case F.Class is
            when F_Integer =>
               return To_String (Prefix) & "U" & Img (F.Length) & "_T";

            when F_Modular =>
               return To_String (Prefix) & "M" & Img (F.Length) & "_T";

            when F_Private =>
               return To_String (F.F_Type);
         end case;
      end Field_Type;

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

      PL (Ctx.P_Spec, Message_Name & "_Size : constant := "
          & Img (Current_Bit_Offset) & ";");

      if Export_Prefix /= null then
         NL (Ctx.P_C);
         Box (Ctx.P_C, Message_Name, Lang_C);

         NL (Ctx.P_C);
         PL (Ctx.P_C, "#define " & Message_Name & "_Size"
             & " " & Img (Current_Bit_Offset, L => Lang_C));
      end if;

      --  Generate accessor declarations and bodies

      for F of Fields loop
         Field_Accessors : declare
            FT          : constant String := Field_Type (F);

            Field_Name  : constant String := To_String (Prefix & F.Name);

            Padded_Name : constant String :=
                            Head (Field_Name,
                                  Length (Prefix) + Max_Field_Name_Length);

            Get_Profile : constant String :=
                            "function  " & Padded_Name
                            & "     (P : System.Address) return "
                            & Field_Type (F);

            Set_Profile : constant String :=
                            "procedure Set_"
                            & Padded_Name
                            & " (P : System.Address; V : "
                            & Field_Type (F) & ")";

            Set_Contract : constant String := "Depends => (null => (P, V))";
            --  Dependency contract that should be used to prevent flow
            --  analysis warnings about useless calls to the imported
            --  procedures, and useless computations of their actual
            --  parameters.

            procedure Generate_M_Decl;
            --  Generate declaration of object M and its address clause

            ---------------------
            -- Generate_M_Decl --
            ---------------------

            procedure Generate_M_Decl is
            begin
               II (Ctx.P_Body);
               PL (Ctx.P_Body,
                 "M : " & Message_Name & " with Address => P, Import;");
            end Generate_M_Decl;

         --  Start of processing for Field_Accessors

         begin
            NL (Ctx.P_Spec);
            PL (Ctx.P_Spec, Get_Profile);
            PL (Ctx.P_Spec, "  with Inline;");
            PL (Ctx.P_Spec, Set_Profile);
            PL (Ctx.P_Spec, "  with Inline, " & Set_Contract & ";");

            if Export_Prefix /= null and then F.Export then
               declare
                  C_Get_Name : constant String :=
                                 Export_Prefix.all & Field_Name;
                  C_Set_Name : constant String  :=
                                 Export_Prefix.all & "Set_" & Field_Name;
                  C_Field_Type : constant String := Field_Type (F, Lang_C);
               begin
                  PL (Ctx.P_Spec,
                      "pragma Export (C, " & Field_Name
                      & ", """ & C_Get_Name & """);");
                  PL (Ctx.P_Spec,
                      "pragma Export (C, Set_" & Field_Name
                      & ", """ & C_Set_Name & """);");

                  NL (Ctx.P_C);
                  PL (Ctx.P_C, "extern " & C_Field_Type);
                  PL (Ctx.P_C,
                      C_Get_Name & " (void *p);");
                  PL (Ctx.P_C, "extern void");
                  PL (Ctx.P_C,
                      C_Set_Name & " (void *p, " & C_Field_Type & " v);");
               end;
            end if;

            NL (Ctx.P_Body);
            PL (Ctx.P_Body, Get_Profile & " is");
            Generate_M_Decl;

            DI (Ctx.P_Body);
            PL (Ctx.P_Body, "begin");
            II (Ctx.P_Body);
            PL (Ctx.P_Body, "return M." & To_String (F.Name) & ";");
            DI (Ctx.P_Body);
            PL (Ctx.P_Body, "end " & Field_Name & ";");

            --  Setter

            NL (Ctx.P_Body);
            PL (Ctx.P_Body, Set_Profile & " is");
            Generate_M_Decl;

            DI (Ctx.P_Body);
            PL (Ctx.P_Body, "begin");
            II (Ctx.P_Body);
            PL (Ctx.P_Body, "M." & To_String (F.Name) & " := V;");
            DI (Ctx.P_Body);
            PL (Ctx.P_Body, "end Set_" & Field_Name & ";");
         end Field_Accessors;
      end loop;

      --  Generate record declaration

      NL (Ctx.P_Private);
      PL (Ctx.P_Private, "type " & Message_Name & " is record");
      II (Ctx.P_Private);

      for F of Fields loop
         PL (Ctx.P_Private,
             Head (To_String (F.Name), Max_Field_Name_Length)
             & " : " & Field_Type (F) & ";");
      end loop;

      DI (Ctx.P_Private);
      PL (Ctx.P_Private, "end record");
      PL (Ctx.P_Private, "with");
      PL (Ctx.P_Private, "  Alignment            => 1,");
      PL (Ctx.P_Private, "  Bit_Order            => System.High_Order_First,");
      PL (Ctx.P_Private, "  Scalar_Storage_Order => System.High_Order_First;");

      --  Generate rep clause

      NL (Ctx.P_Private);
      PL (Ctx.P_Private, "for " & Message_Name & " use record");
      II (Ctx.P_Private);

      for F of Fields loop
         PL (Ctx.P_Private,
                   Head (To_String (F.Name), Max_Field_Name_Length)
                   & " at "    & Img (4 * (F.First_Bit / 32))
                   & " range " & Img (F.First_Bit mod 32)
                   & " .. "    & Img (F.First_Bit mod 32 + F.Length - 1)
                   & ";");
      end loop;

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

      procedure Prelude (U : in out Unit; L : Lang := Lang_Ada);
      --  Output standard text at the top of every unit

      -------------
      -- Prelude --
      -------------

      procedure Prelude (U : in out Unit; L : Lang := Lang_Ada) is
         procedure Comment (S : String);
         --  Output S as a comment

         -------------
         -- Comment --
         -------------

         procedure Comment (S : String) is
         begin
            case L is
               when Lang_Ada =>
                  PL (U, "--  " & S);
               when Lang_C =>
                  PL (U, "/* " & S & (1 .. 78 - S'Length - 5 => ' ') & "*/");
            end case;
         end Comment;

         --  Start of processing for Prelude

      begin
         Comment ("This file has been automatically generated from "
                  & Input_Name.all);
         Comment ("DO NOT EDIT!!!");

         if L = Lang_Ada then
            NL (U);
            PL (U, "pragma Warnings (Off);");
            PL (U, "pragma Style_Checks (""NM32766"");");
            PL (U, "pragma Ada_2012;");
            NL (U);
         end if;
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

      Ctx.Types_Unit := To_Unbounded_String (Get_Attribute (N, "types_unit"));

      Prelude (Ctx.P_Spec);
      Prelude (Ctx.P_Body);

      if Export_Prefix /= null then
         Prelude (Ctx.P_C, Lang_C);
      end if;

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
      NL (Ctx.P_Spec);
      PL (Ctx.P_Spec, "pragma Pure;");

      II (Ctx.P_Private);

      PL (Ctx.P_Body, "package body " & Package_Name & " with");
      PL (Ctx.P_Body, "  SPARK_Mode => Off");
      PL (Ctx.P_Body, "is");
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

      Generate_Output : declare
         use Ada.Streams.Stream_IO;

         Out_F : Ada.Streams.Stream_IO.File_Type;
      begin
         Create (Out_F, Out_File, Output_Prefix.all & ".ada");
         Dump (Ctx.P_Spec,    Out_F);
         Dump (Ctx.P_Private, Out_F);
         Dump (Ctx.P_Body,    Out_F);
         Close (Out_F);

         if Export_Prefix /= null then
            Create (Out_F, Out_File, Output_Prefix.all & ".h");
            Dump (Ctx.P_C, Out_F);
            Close (Out_F);
         end if;
      end Generate_Output;
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

   -----------
   -- Usage --
   -----------

   procedure Usage is
   begin
      Put_Line
        (Standard_Error,
         "Usage: tranxgen [-o OUTPUT_DIR] [-x EXPORT_PREFIX] [-h] INPUT.xml");
      OS_Exit (0);
   end Usage;

   Input : File_Input;
   Read  : DOM.Readers.Tree_Reader;
   Doc   : Document;
   Root  : DOM.Core.Element;

--  Start of processing for Tranxgen

begin
   loop
      case Getopt ("o: x: h") is
         when ASCII.NUL =>
            exit;

         when 'o' =>
            Output_Dir := new String'(Parameter);

         when 'x' =>
            Export_Prefix := new String'(Parameter);

         when 'h' =>
            Usage;

         when others =>
            raise Program_Error;
            --  Cannot occur
      end case;
   end loop;

   if Output_Dir = null then
      Output_Dir := new String'(".");
   end if;

   Input_Name := new String'(Get_Argument);

   if Index (Input_Name.all, ".xml") /= Input_Name'Last - 3 then
      Put_Line (Standard_Error, "input file name must end with "".xml""");
      OS_Exit (1);
   end if;
   Output_Prefix :=
     new String'(Output_Dir.all & '/'
                 & Simple_Name
                   (Input_Name
                      (Input_Name'First .. Input_Name'Last - 4)));

   Open (Input_Name.all, Input);

   Parse (Read, Input);

   Doc  := Get_Tree (Read);
   Root := Get_Element (Doc);

   Process_Package (Root);

   Free (Read);
   Close (Input);

end Tranxgen;
