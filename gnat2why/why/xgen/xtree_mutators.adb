------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       X T R E E _ M U T A T O R S                        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2019, AdaCore                     --
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

with Why.Sinfo;      use Why.Sinfo;
with Xtree_Tables;   use Xtree_Tables;
with Xkind_Tables;   use Xkind_Tables;

package body Xtree_Mutators is

   Node_Id_Param : constant Wide_String := "Id";
   --  Name of a formal parameter that is common to all mutators; this
   --  is the id of the node whose children are modified through the
   --  corresponding mutator.

   Element_Param : constant Wide_String := "New_Item";
   --  Name of a formal parameter that is common to all append/prepend
   --  routines; this is the id of the new node to append to the list.

   procedure Print_Setter_Implementation
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      FI   : Field_Info);
   pragma Precondition (not Is_List (FI));
   --  Print setter implementation for the given node child
   --  (from the declarative part of the mutator to the end
   --  of its sequence of statement. Not included: the subprogram
   --  specification, the "is" keyword and the "end designator;"
   --  part).

   procedure Print_Mutator_Kind_Bodies
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);
   --  Print mutator bodies for the given node kind

   procedure Print_Mutator_Kind_Declarations
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);
   --  Print mutator declarations for the given node kind

   procedure Print_Setter_Specification
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      FI   : Field_Info;
      IK   : Id_Kind);
   pragma Precondition (not Is_List (FI));
   --  Print setter specification for the given node child

   procedure Print_Mutator_Precondition (O : in out Output_Record);
   --  Print mutator precondition for the given node child.
   --  Note that this precondition can be replaced nicely
   --  replaced by a subtype predicate on ids; when subtype
   --  predicates are supported by GNAT, it will be a good time
   --  to do the substitution.

   procedure Print_Mutator_Specification
     (O           : in out Output_Record;
      Name        : Wide_String;
      Param_Type  : Wide_String;
      Field_Param : Wide_String;
      Field_Type  : Wide_String);
   --  Print mutator specification from its formals. the mutator
   --  may be a setter, but it may as well be an append/prepend
   --  operations (when the considered child is a node list);
   --  this procedure makes no assumption on the final nature of
   --  this mutator. It just suppose that it is a procedure with
   --  two parameters, whose formal name/type name are given in
   --  Name/Param_Type and Field_Param/Field_Type.

   procedure Print_List_Op_Specification
     (O       : in out Output_Record;
      Kind    : Why_Node_Kind;
      FI      : Field_Info;
      IK      : Id_Kind;
      List_Op : List_Op_Kind);
   pragma Precondition (Is_List (FI));
   --  Print specification of the given operation on node lists,
   --  for the a child of any node of the given kind. e.g.
   --  append operations on child of a given node, assuming that
   --  this child has List or OList for multiplicity modifier.

   procedure Print_List_Op_Implementation
     (O       : in out Output_Record;
      Kind    : Why_Node_Kind;
      FI      : Field_Info;
      List_Op : List_Op_Kind);
   pragma Precondition (Is_List (FI));
   --  Print implementation of the given operation on node lists
   --  (from the declarative part of the mutator to the end
   --  of its sequence of statement. Not included: the subprogram
   --  specification, the "is" keyword and the "end designator;"
   --  part).

   procedure Print_Update_Validity_Status
     (O       : in out Output_Record;
      Kind    : Why_Node_Kind);
   --  Print an expression that updates the validity status of a node of
   --  the given kind.

   ----------------------------------
   -- Print_List_Op_Implementation --
   ----------------------------------

   procedure Print_List_Op_Implementation
     (O       : in out Output_Record;
      Kind    : Why_Node_Kind;
      FI      : Field_Info;
      List_Op : List_Op_Kind) is
   begin
      Relative_Indent (O, 3);
      PL (O, "Node : constant Why_Node :=");
      PL (O, "         Get_Node (+" & Node_Id_Param & ");");
      Relative_Indent (O, -3);
      PL (O, "begin");
      Relative_Indent (O, 3);
      PL (O, List_Op_Name (List_Op)
          & " (Node." & Field_Name (FI)
          & ", +" & Element_Param & ");");
      Print_Update_Validity_Status (O, Kind);
      Relative_Indent (O, -3);
   end Print_List_Op_Implementation;

   --------------------------------
   -- Print_List_Op_Specification --
   --------------------------------

   procedure Print_List_Op_Specification
     (O       : in out Output_Record;
      Kind    : Why_Node_Kind;
      FI      : Field_Info;
      IK      : Id_Kind;
      List_Op : List_Op_Kind) is
   begin
      Print_Mutator_Specification
        (O           => O,
         Name        => List_Op_Name (Kind, FI, List_Op),
         Param_Type  => Id_Subtype (Kind, IK),
         Field_Param => Element_Param,
         Field_Type  => Element_Type_Name (FI, Derived));
   end Print_List_Op_Specification;

   --------------------------
   -- Print_Mutator_Bodies --
   --------------------------

   procedure Print_Mutator_Bodies (O : in out Output_Record) is
      First : Boolean := True;
   begin
      for J in Valid_Kind'Range loop
         if Is_Mutable (J)
           and then Has_Variant_Part (J)
         then
            if First then
               First := False;
            else
               NL (O);
            end if;

            Print_Mutator_Kind_Bodies (O, J);
         end if;
      end loop;
   end Print_Mutator_Bodies;

   --------------------------------
   -- Print_Mutator_Declarations --
   --------------------------------

   procedure Print_Mutator_Declarations (O : in out Output_Record)
   is
      First : Boolean := True;
   begin
      for J in Valid_Kind'Range loop
         if Has_Variant_Part (J)
           and then Is_Mutable (J)
         then
            if First then
               First := False;
            else
               NL (O);
            end if;

            Print_Mutator_Kind_Declarations (O, J);
         end if;
      end loop;
   end Print_Mutator_Declarations;

   -------------------------------
   -- Print_Mutator_Kind_Bodies --
   -------------------------------

   procedure Print_Mutator_Kind_Bodies
     (O    : in out Output_Record;
      Kind : Why_Node_Kind)
   is
      use Node_Lists;

      procedure Print_Mutator_Body
        (FI : Field_Info;
         IK : Id_Kind);
      --  Print mutator body for node child for the given descriptor
      --  (and the given id kind for the father node).

      ------------------------
      -- Print_Mutator_Body --
      ------------------------

      procedure Print_Mutator_Body
        (FI : Field_Info;
         IK : Id_Kind) is
      begin
         if not Is_List (FI) then
            declare
               MN : constant Wide_String := Mutator_Name (Kind, FI);
            begin
               Print_Box (O, MN);
               NL (O);

               Print_Setter_Specification (O, Kind, FI, IK);
               NL (O);
               PL (O, "is");
               Print_Setter_Implementation (O, Kind, FI);
               PL (O, "end " & MN & ";");
            end;
         else
            for List_Op in List_Op_Kind'Range loop
               declare
                  LON : constant Wide_String :=
                          List_Op_Name (Kind, FI, List_Op);
               begin
                  Print_Box (O, LON);
                  NL (O);

                  Print_List_Op_Specification (O, Kind, FI, IK, List_Op);
                  NL (O);
                  PL (O, "is");
                  Print_List_Op_Implementation (O, Kind, FI, List_Op);
                  PL (O, "end " & LON & ";");

                  if List_Op /= List_Op_Kind'Last then
                     NL (O);
                  end if;
               end;
            end loop;
         end if;
      end Print_Mutator_Body;

      First_Iteration : Boolean := True;

   --  Start of Processing for Print_Mutator_Kind_Bodies

   begin
      if Has_Variant_Part (Kind) then
         for FI of Why_Tree_Info (Kind).Fields loop
            if First_Iteration then
               First_Iteration := False;
            else
               NL (O);
            end if;

            Print_Mutator_Body (FI, Unchecked);
            NL (O);
            Print_Mutator_Body (FI, Derived);
         end loop;
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

      procedure Print_Mutator_Kind_Declaration
        (FI : Field_Info;
         IK : Id_Kind);
      --  Print mutator declaration for node child whose descriptor
      --  is at Position (and whose father has kind Kind).

      -------------------------------------
      -- Print_Mutator_Kind_Declaration --
      -------------------------------------

      procedure Print_Mutator_Kind_Declaration
        (FI : Field_Info;
         IK : Id_Kind) is
      begin
         if not Is_List (FI) then
            Print_Setter_Specification (O, Kind, FI, IK);
            PL (O, " with");
            Relative_Indent (O, 2);
            Print_Mutator_Precondition (O);
            Relative_Indent (O, -2);
            PL (O, ";");
         else
            for List_Op in List_Op_Kind'Range loop
               Print_List_Op_Specification (O, Kind, FI, IK, List_Op);
               PL (O, " with");
               Relative_Indent (O, 2);
               Print_Mutator_Precondition (O);
               Relative_Indent (O, -2);
               PL (O, ";");

               if List_Op /= List_Op_Kind'Last then
                  NL (O);
               end if;
            end loop;
         end if;
      end Print_Mutator_Kind_Declaration;

      First_Iteration : Boolean := True;

   --  Start of Processing for Print_Mutator_Kind_Declarations

   begin
      if Has_Variant_Part (Kind) then
         for FI of Why_Tree_Info (Kind).Fields loop
            if First_Iteration then
               First_Iteration := False;
            else
               NL (O);
            end if;

            Print_Mutator_Kind_Declaration (FI, Unchecked);
            NL (O);
            Print_Mutator_Kind_Declaration (FI, Derived);
         end loop;
      end if;
   end Print_Mutator_Kind_Declarations;

   --------------------------------
   -- Print_Mutator_Precondition --
   --------------------------------

   procedure Print_Mutator_Precondition (O : in out Output_Record) is
   begin
      P (O, "Pre => (Is_Root (+" & Node_Id_Param & "))");
   end Print_Mutator_Precondition;

   ---------------------------------
   -- Print_Mutator_Specification --
   ---------------------------------

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

   ---------------------------------
   -- Print_Setter_Implementation --
   ---------------------------------

   procedure Print_Setter_Implementation
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      FI   : Field_Info) is
   begin
      Relative_Indent (O, 3);
      PL (O, "Node : Why_Node := Get_Node (+" & Node_Id_Param & ");");
      Relative_Indent (O, -3);
      PL (O, "begin");
      Relative_Indent (O, 3);
      P (O, "Node." & Field_Name (FI) & " := ");

      if Is_Why_Id (FI) then
         P (O, "+");
      end if;

      PL (O, Param_Name (FI) & ";");
      PL (O, "Set_Node (+" & Node_Id_Param & ", Node);");

      if Is_Why_Id (FI) then
         PL (O,
             "Set_Link (Why_Node_Id (" & Param_Name (FI) & "), +"
             & Node_Id_Param & ");");
         Print_Update_Validity_Status (O, Kind);
      end if;

      Relative_Indent (O, -3);
   end Print_Setter_Implementation;

   --------------------------------
   -- Print_Setter_Specification --
   --------------------------------

   procedure Print_Setter_Specification
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      FI   : Field_Info;
      IK   : Id_Kind) is
   begin
      Print_Mutator_Specification
        (O           => O,
         Name        => Mutator_Name (Kind, FI),
         Param_Type  => Id_Subtype (Kind, IK),
         Field_Param => Param_Name (FI),
         Field_Type  => Type_Name (FI, Derived));
   end Print_Setter_Specification;

   ----------------------------------
   -- Print_Update_Validity_Status --
   ----------------------------------

   procedure Print_Update_Validity_Status
     (O       : in out Output_Record;
      Kind    : Why_Node_Kind) is
   begin
      PL (O, "Update_Validity_Status");
      PL (O, "  (+" & Node_Id_Param & ",");
      PL (O, "   " & Tree_Check (Mixed_Case_Name (Kind), Id_One)
          & " (Why_Node_Id (" & Node_Id_Param & ")));");
   end Print_Update_Validity_Status;

end Xtree_Mutators;
