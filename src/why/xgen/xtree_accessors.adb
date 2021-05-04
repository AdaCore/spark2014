------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      X T R E E _ A C C E S S O R S                       --
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

with Why.Sinfo;    use Why.Sinfo;
with Xtree_Tables; use Xtree_Tables;
with Xkind_Tables; use Xkind_Tables;

package body Xtree_Accessors is

   Node_Id_Param : constant String := "Id";
   --  Name of the formal parameter of all accessors; this will be the
   --  id of the node whose children are accessible through the
   --  corresponding accessor.

   procedure Print_Accessor_Parameterized_Expressions
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      IK   : Id_Kind);
   --  Print the parameterized expressions defining node accessors

   procedure Print_Accessor_Specification
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      FI   : Field_Info;
      IK   : Id_Kind);
   --  Print the accessor spec for the given node child

   procedure Print_Accessor_Specification
     (O           : in out Output_Record;
      Name        : String;
      Param_Type  : String;
      Return_Type : String);
   --  Print an accessor specification from the name of its formals

   procedure Print_Accessor_Expression
     (O    : in out Output_Record;
      FI   : Field_Info;
      IK   : Id_Kind);
   --  Print the accessor expression for the given node child

   procedure Print_Accessor_Kind_Declarations
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      IK   : Id_Kind);
   --  Print accessor declarations for the given node kind

   ---------------------------
   -- Print_Accessor_Bodies --
   ---------------------------

   procedure Print_Accessor_Bodies
     (O : in out Output_Record)
   is
      use Node_Lists;

      procedure Print_Accessor_Bodies (IK : Id_Kind);
      --  Print accessor bodies for the given id kind

      ---------------------------
      -- Print_Accessor_Bodies --
      ---------------------------

      procedure Print_Accessor_Bodies (IK : Id_Kind) is
      begin
         for J in Valid_Kind'Range loop
            if Has_Variant_Part (J) then
               Print_Accessor_Parameterized_Expressions (O, J, IK);

               if J /= Why_Tree_Info'Last then
                  NL (O);
               end if;
            end if;
         end loop;
      end Print_Accessor_Bodies;

   --  Start of Processing for Print_Accessor_Bodies

   begin
      for FI of Common_Fields.Fields loop
         if Field_Kind (FI) in Field_Common | Field_Domain then
            Print_Accessor_Specification
              (O           => O,
               Name        => Accessor_Name (W_Unused_At_Start, Derived, FI),
               Param_Type  => "Why_Node_Id",
               Return_Type => Type_Name (FI, Derived));
            PL (O, " is");
            Relative_Indent (O, 2);
            Print_Accessor_Expression (O, FI, Derived);
            PL (O, ";");
            Relative_Indent (O, -2);
            NL (O);
         end if;
      end loop;

      Print_Accessor_Bodies (Unchecked);
      NL (O);
      Print_Accessor_Bodies (Derived);
   end Print_Accessor_Bodies;

   ---------------------------------
   -- Print_Accessor_Declarations --
   ---------------------------------

   procedure Print_Accessor_Declarations (O : in out Output_Record)
   is
      use Node_Lists;

      procedure Print_Accessor_Declarations (IK : Id_Kind);
      --  Print accessor declarations for the given id kind

      ---------------------------------
      -- Print_Accessor_Declarations --
      ---------------------------------

      procedure Print_Accessor_Declarations (IK : Id_Kind) is
      begin
         for J in Valid_Kind'Range loop
            if Has_Variant_Part (J) then
               Print_Accessor_Kind_Declarations (O, J, IK);

               if J /= Why_Tree_Info'Last then
                  NL (O);
               end if;
            end if;
         end loop;
      end Print_Accessor_Declarations;

   --  Start of Processing for Print_Accessor_Declarations

   begin
      for FI of Common_Fields.Fields loop
         if Field_Kind (FI) in Field_Common | Field_Domain then
            Print_Accessor_Specification
              (O           => O,
               Name        => Accessor_Name (W_Unused_At_Start, Derived, FI),
               Param_Type  => "Why_Node_Id",
               Return_Type => Type_Name (FI, Derived));
            PL (O, ";");
            NL (O);
         end if;
      end loop;

      Print_Accessor_Declarations (Unchecked);
      NL (O);
      Print_Accessor_Declarations (Derived);
   end Print_Accessor_Declarations;

   --------------------------------
   -- Print_Accessor_Expressions --
   --------------------------------

   procedure Print_Accessor_Expression
     (O    : in out Output_Record;
      FI   : Field_Info;
      IK   : Id_Kind) is
   begin
      if Is_Why_Id (FI) then
         declare
            M : constant Id_Multiplicity :=
                  (if IK in Regular .. Derived then
                     Multiplicity (FI)
                   else
                     (if Multiplicity (FI) = Id_Some
                        or else Multiplicity (FI) = Id_Set
                      then
                        Id_Set
                      else
                        Id_Lone));
         begin
            P (O,
               "(" & Id_Subtype (Node_Kind (FI), IK, M)
               & " (Get_Node (+" & Node_Id_Param & ")."
               & Field_Name (FI) & "))");
         end;
      else
         P (O, "(Get_Node (+" & Node_Id_Param & ")."
            & Field_Name (FI) & ")");
      end if;
   end Print_Accessor_Expression;

   ----------------------------------------------
   -- Print_Accessor_Parameterized_Expressions --
   ----------------------------------------------

   procedure Print_Accessor_Parameterized_Expressions
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      IK   : Id_Kind)
   is
      use Node_Lists;

      procedure Print_Accessor_Parameterized_Expression (Position : Cursor);
      --  Print the parameterized expression that implements the accessor
      --  for a node child whose descriptor is at Position (and whose
      --  father has kind Kind)

      ---------------------------------------------
      -- Print_Accessor_Parameterized_Expression --
      ---------------------------------------------

      procedure Print_Accessor_Parameterized_Expression (Position : Cursor) is
         FI : constant Field_Info := Element (Position);
      begin
         Print_Accessor_Specification (O, Kind, FI, IK);
         PL (O, " is");
         Relative_Indent (O, 2);
         Print_Accessor_Expression (O, FI, IK);
         PL (O, ";");
         Relative_Indent (O, -2);

         if Next (Position) /= No_Element then
            NL (O);
         end if;
      end Print_Accessor_Parameterized_Expression;

   --  Start of Processing for Print_Accessor_Parameterized_Expressions

   begin
      if Has_Variant_Part (Kind) then
         Why_Tree_Info (Kind).Fields.Iterate
           (Print_Accessor_Parameterized_Expression'Access);
      end if;
   end Print_Accessor_Parameterized_Expressions;

   ----------------------------------------------
   -- Print_Accessor_Parameterized_Expressions --
   ----------------------------------------------

   procedure Print_Accessor_Kind_Declarations
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      IK   : Id_Kind)
   is
      use Node_Lists;

      procedure Print_Accessor_Kind_Declaration (Position : Cursor);
      --  Print Accessor declaration for a node child whose descriptor
      --  is at Position (and whose father has kind Kind).

      -------------------------------------
      -- Print_Accessor_Kind_Declaration --
      -------------------------------------

      procedure Print_Accessor_Kind_Declaration (Position : Cursor) is
         FI : constant Field_Info := Element (Position);
      begin
         Print_Accessor_Specification (O, Kind, FI, IK);
         PL (O, ";");

         if Next (Position) /= No_Element then
            NL (O);
         end if;
      end Print_Accessor_Kind_Declaration;

   --  Start of Processing for Print_Accessor_Kind_Declarations

   begin
      if Has_Variant_Part (Kind) then
         Why_Tree_Info (Kind).Fields.Iterate
           (Print_Accessor_Kind_Declaration'Access);
      end if;
   end Print_Accessor_Kind_Declarations;

   ----------------------------------
   -- Print_Accessor_Specification --
   ----------------------------------

   procedure Print_Accessor_Specification
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      FI   : Field_Info;
      IK   : Id_Kind) is
   begin
      Print_Accessor_Specification
        (O           => O,
         Name        => Accessor_Name (Kind, IK, FI),
         Param_Type  => Id_Subtype (Kind, IK),
         Return_Type => Type_Name (FI, IK));
   end Print_Accessor_Specification;

   procedure Print_Accessor_Specification
     (O           : in out Output_Record;
      Name        : String;
      Param_Type  : String;
      Return_Type : String) is
   begin
      PL (O, "function " & Name);
      PL (O, "  (" & Node_Id_Param & " : " & Param_Type  & ")");
      P  (O, "  return " & Return_Type);
   end Print_Accessor_Specification;

end Xtree_Accessors;
