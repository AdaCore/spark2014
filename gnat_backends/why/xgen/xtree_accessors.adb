------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      X T R E E _ A C C E S S O R S                       --
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

package body Xtree_Accessors is

   Node_Id_Param : constant Wide_String := "Id";

   procedure Print_Accessor_Functional_Expressions
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);

   procedure Print_Accessor_Specification
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      FI   : Field_Info);

   procedure Print_Accessor_Specification
     (O           : in out Output_Record;
      Name        : Wide_String;
      Param_Type  : Wide_String;
      Return_Type :  Wide_String);

   procedure Print_Accessor_Expression
     (O    : in out Output_Record;
      FI   : Field_Info);

   ---------------------------------
   -- Print_Accessor_Declarations --
   ---------------------------------

   procedure Print_Accessor_Declarations  (O : in out Output_Record)
   is
      use Node_Lists;

      procedure Print_Common_Field_Accessor (Position : Cursor);

      ---------------------------------
      -- Print_Common_Field_Accessor --
      ---------------------------------

      procedure Print_Common_Field_Accessor (Position : Cursor) is
         FI : constant Field_Info := Element (Position);
      begin
         Print_Accessor_Specification
           (O           => O,
            Name        => Accessor_Name (W_Unused_At_Start, FI),
            Param_Type  => "Why_Node_Id",
            Return_Type => Id_Type_Name (FI));
         PL (O, " is");
         Relative_Indent (O, 2);
         Print_Accessor_Expression (O, FI);
         PL (O, ";");
         Relative_Indent (O, -2);

         if Next (Position) /= No_Element then
            NL (O);
         end if;
      end Print_Common_Field_Accessor;

   begin
      Common_Fields.Fields.Iterate (Print_Common_Field_Accessor'Access);
      NL (O);

      for J in Valid_Kind'Range loop
         if Has_Variant_Part (J) then
            Print_Accessor_Functional_Expressions (O, J);

            if J /= Why_Tree_Info'Last then
               NL (O);
            end if;
         end if;
      end loop;
   end Print_Accessor_Declarations;

   --------------------------------
   -- Print_Accessor_Expressions --
   --------------------------------

   procedure Print_Accessor_Expression
     (O    : in out Output_Record;
      FI   : Field_Info) is
   begin
      P (O, "(Get_Node (" & Node_Id_Param & ")." & Field_Name (FI) & ")");
   end Print_Accessor_Expression;

   -------------------------------------------
   -- Print_Accessor_Functional_Expressions --
   -------------------------------------------

   procedure Print_Accessor_Functional_Expressions
     (O    : in out Output_Record;
      Kind : Why_Node_Kind)
   is
      use Node_Lists;

      procedure Print_Accessor_Functional_Expression (Position : Cursor);

      ------------------------------------------
      -- Print_Accessor_Functional_Expression --
      ------------------------------------------

      procedure Print_Accessor_Functional_Expression (Position : Cursor) is
         FI : constant Field_Info := Element (Position);
      begin
         Print_Accessor_Specification (O, Kind, FI);
         PL (O, " is");
         Relative_Indent (O, 2);
         Print_Accessor_Expression (O, FI);
         PL (O, ";");
         Relative_Indent (O, -2);

         if Next (Position) /= No_Element then
            NL (O);
         end if;
      end Print_Accessor_Functional_Expression;

   begin
      if Has_Variant_Part (Kind) then
         Why_Tree_Info (Kind).Fields.Iterate
           (Print_Accessor_Functional_Expression'Access);
      end if;
   end Print_Accessor_Functional_Expressions;

   ----------------------------------
   -- Print_Accessor_Specification --
   ----------------------------------

   procedure Print_Accessor_Specification
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      FI   : Field_Info) is
   begin
      Print_Accessor_Specification
        (O           => O,
         Name        => Accessor_Name (Kind, FI),
         Param_Type  => Id_Type_Name (Kind),
         Return_Type => Id_Type_Name (FI));
   end Print_Accessor_Specification;

   procedure Print_Accessor_Specification
     (O           : in out Output_Record;
      Name        : Wide_String;
      Param_Type  : Wide_String;
      Return_Type :  Wide_String) is
   begin
      PL (O, "function " & Name);
      PL (O, "  (" & Node_Id_Param & " : " & Param_Type  & ")");
      P  (O, "  return " & Return_Type);
   end Print_Accessor_Specification;

end Xtree_Accessors;
