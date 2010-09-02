------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       X T R E E _ M U T A T O R S                        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute it and/or modify it   --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers; use Ada.Containers;
with Why.Sinfo;      use Why.Sinfo;
with Xtree_Tables;   use Xtree_Tables;

package body Xtree_Mutators is

   Node_Id_Param : constant Wide_String := "Id";
   --  Name of a formal parameter that is common to all mutators; this
   --  is the id of the node whose children are modified through the
   --  corresponding mutator.

   procedure Print_Mutator_Implementation
     (O    : in out Output_Record;
      FI   : Field_Info);
   --  Print mutator implementation for the given node child
   --  (from the declarative part of the mutator to the end
   --  of its sequence of statement. Not included: the subprogram
   --  specification, the "is" keyword and the "end designator;"
   --  part)

   procedure Print_Mutator_Kind_Bodies
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);
   --  Print mutator bodies for the given node kind

   procedure Print_Mutator_Kind_Declarations
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);
   --  Print mutator declarations for the given node kind

   procedure Print_Mutator_Specification
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      FI   : Field_Info);
   --  Print mutator specification for the given node child

   procedure Print_Mutator_Specification
     (O           : in out Output_Record;
      Name        : Wide_String;
      Param_Type  : Wide_String;
      Field_Param : Wide_String;
      Field_Type  : Wide_String);
   --  Print mutator specification from its formals

   --------------------------
   -- Print_Mutator_Bodies --
   --------------------------

   procedure Print_Mutator_Bodies  (O : in out Output_Record) is
      use Node_Lists;

      procedure Print_Common_Field_Mutator (Position : Cursor);
      --  Print mutator body for common field whose descriptor
      --  is at Position.

      --------------------------------
      -- Print_Common_Field_Mutator --
      --------------------------------

      procedure Print_Common_Field_Mutator (Position : Cursor) is
         FI : constant Field_Info := Element (Position);
         MN : constant Wide_String := Mutator_Name (W_Unused_At_Start, FI);
      begin
         Print_Box (O, MN);
         NL (O);

         Print_Mutator_Specification
           (O           => O,
            Name        => MN,
            Param_Type  => "Why_Node_Id",
            Field_Param => Param_Name (FI),
            Field_Type  => Id_Type_Name (FI));
         NL (O);
         PL (O, "is");
         Print_Mutator_Implementation (O, FI);
         PL (O, "end " & MN & ";");

         if Next (Position) /= No_Element then
            NL (O);
         end if;
      end Print_Common_Field_Mutator;

   --  Start of Processing for Print_Mutator_Bodies

   begin
      Common_Fields.Fields.Iterate (Print_Common_Field_Mutator'Access);
      NL (O);

      for J in Valid_Kind'Range loop
         if Has_Variant_Part (J) then
            Print_Mutator_Kind_Bodies (O, J);

            if J /= Why_Tree_Info'Last then
               NL (O);
            end if;
         end if;
      end loop;
   end Print_Mutator_Bodies;

   --------------------------------
   -- Print_Mutator_Declarations --
   --------------------------------

   procedure Print_Mutator_Declarations  (O : in out Output_Record) is
      use Node_Lists;

      procedure Print_Common_Field_Mutator (Position : Cursor);
      --  Print mutator declaration for common field whose descriptor
      --  is at Position.

      --------------------------------
      -- Print_Common_Field_Mutator --
      --------------------------------

      procedure Print_Common_Field_Mutator (Position : Cursor) is
         FI : constant Field_Info := Element (Position);
      begin
         Print_Mutator_Specification
           (O           => O,
            Name        => Mutator_Name (W_Unused_At_Start, FI),
            Param_Type  => "Why_Node_Id",
            Field_Param => Param_Name (FI),
            Field_Type  => Id_Type_Name (FI));
         PL (O, ";");

         if Next (Position) /= No_Element then
            NL (O);
         end if;
      end Print_Common_Field_Mutator;

   --  Start of Processing for Print_Mutator_Declarations

   begin
      Common_Fields.Fields.Iterate (Print_Common_Field_Mutator'Access);
      NL (O);

      for J in Valid_Kind'Range loop
         if Has_Variant_Part (J) then
            Print_Mutator_Kind_Declarations (O, J);

            if J /= Why_Tree_Info'Last then
               NL (O);
            end if;
         end if;
      end loop;
   end Print_Mutator_Declarations;

   ----------------------------------
   -- Print_Mutator_Implementation --
   ----------------------------------

   procedure Print_Mutator_Implementation
     (O    : in out Output_Record;
      FI   : Field_Info) is
   begin
      PL (O, "   Node : Why_Node := Get_Node (" & Node_Id_Param & ");");
      PL (O, "begin");
      PL (O, "   Node." & Field_Name (FI) & " := " & Param_Name (FI) & ";");
      PL (O, "   Set_Node (" & Node_Id_Param &", Node);");
      --  ??? Missing handling for Checked (should be updated
      --  if the node is valid after the assignment)
   end Print_Mutator_Implementation;

   -------------------------------
   -- Print_Mutator_Kind_Bodies --
   -------------------------------

   procedure Print_Mutator_Kind_Bodies
     (O    : in out Output_Record;
      Kind : Why_Node_Kind)
   is
      use Node_Lists;

      procedure Print_Mutator_Body (Position : Cursor);
      --  Print mutator body for node child whose descriptor
      --  is at Position (and whose father has kind Kind).

      ------------------------
      -- Print_Mutator_Body --
      ------------------------

      procedure Print_Mutator_Body (Position : Cursor) is
         FI : constant Field_Info := Element (Position);
         MN : constant Wide_String := Mutator_Name (Kind, FI);
      begin
         Print_Box (O, MN);
         NL (O);

         Print_Mutator_Specification (O, Kind, FI);
         NL (O);
         PL (O, "is");
         Print_Mutator_Implementation (O, FI);
         PL (O, "end " & MN & ";");

         if Next (Position) /= No_Element then
            NL (O);
         end if;
      end Print_Mutator_Body;

   --  Start of Processing for Print_Mutator_Kind_Bodies

   begin
      if Has_Variant_Part (Kind) then
         Why_Tree_Info (Kind).Fields.Iterate
           (Print_Mutator_Body'Access);
      end if;
   end Print_Mutator_Kind_Bodies;

   -------------------------------------
   -- Print_Mutator_Kind_Declarations --
   -------------------------------------

   procedure Print_Mutator_Kind_Declarations
     (O    : in out Output_Record;
      Kind : Why_Node_Kind)
   is
      use Node_Lists;

      procedure Print_Mutator_Kind_Declaration (Position : Cursor);
      --  Print mutator declaration for node child whose descriptor
      --  is at Position (and whose father has kind Kind).

      -------------------------------------
      -- Print_Mutator_Kind_Declaration --
      -------------------------------------

      procedure Print_Mutator_Kind_Declaration (Position : Cursor) is
         FI : constant Field_Info := Element (Position);
      begin
         Print_Mutator_Specification (O, Kind, FI);
         PL (O, ";");

         if Next (Position) /= No_Element then
            NL (O);
         end if;
      end Print_Mutator_Kind_Declaration;

   --  Start of Processing for Print_Mutator_Kind_Declarations

   begin
      if Has_Variant_Part (Kind) then
         Why_Tree_Info (Kind).Fields.Iterate
           (Print_Mutator_Kind_Declaration'Access);
      end if;
   end Print_Mutator_Kind_Declarations;

   ---------------------------------
   -- Print_Mutator_Specification --
   ---------------------------------

   procedure Print_Mutator_Specification
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      FI   : Field_Info) is
   begin
      Print_Mutator_Specification
        (O           => O,
         Name        => Mutator_Name (Kind, FI),
         Param_Type  => Unchecked_Id_Type_Name (Kind),
         Field_Param => Param_Name (FI),
         Field_Type  => Unchecked_Id_Type_Name (FI));
   end Print_Mutator_Specification;

   procedure Print_Mutator_Specification
     (O           : in out Output_Record;
      Name        : Wide_String;
      Param_Type  : Wide_String;
      Field_Param : Wide_String;
      Field_Type  : Wide_String)
   is
      NIPL : constant Natural := Node_Id_Param'Length;
      FPL  : constant Natural := Field_Param'Length;
      Max  : constant Natural := Natural'Max (NIPL, FPL);
   begin
      PL (O, "procedure " & Name);
      P (O, "  (" & Node_Id_Param);
      for J in NIPL .. Max loop
         P (O, " ");
      end loop;
      PL (O, ": " & Param_Type  & ";");
      P (O, "   " & Field_Param);
      for J in FPL .. Max loop
         P (O, " ");
      end loop;
      P (O, ": " & Field_Type  & ")");
   end Print_Mutator_Specification;

end Xtree_Mutators;
