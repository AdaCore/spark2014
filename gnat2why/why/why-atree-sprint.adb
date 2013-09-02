------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                     W H Y - A T R E E - S P R I N T                      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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

with Ada.Containers;      use Ada.Containers;

with Errout;              use Errout;
with Namet;               use Namet;
with String_Utils;        use String_Utils;
with Uintp;               use Uintp;

with Gnat2Why.Nodes;      use Gnat2Why.Nodes;
with Why.Inter;           use Why.Inter;
with Why.Images;          use Why.Images;
with Why.Conversions;     use Why.Conversions;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Ada.Directories;
with Ada.Direct_IO;
with GNAT.Regpat;
with GNAT.OS_Lib; use GNAT.OS_Lib;
with Ada.Strings.Unbounded;

package body Why.Atree.Sprint is

   O : Output_Id := Stdout;

   procedure Print_List
     (State     : in out Printer_State'Class;
      List_Id   : Why_Node_List;
      Separator : String := ", ";
      Newline   : Boolean := False);
   --  Print a node list on current output, separating each element
   --  by a given separator, optionally followed by a new line.

   procedure Print_Label_List
     (State   : in out Printer_State'Class;
      List_Id : Why_Node_List);
   --  Print a list of labels, each one with quotes, and separated by space

   ----------------------
   -- Print_Label_List --
   ----------------------

   procedure Print_Label_List
     (State   : in out Printer_State'Class;
      List_Id : Why_Node_List)
   is
      use Node_Lists;
      L         : constant List := Get_List (List_Id);
      Position  : Cursor := First (L);
      pragma Unreferenced (State);
   begin
      while Position /= No_Element loop
         P (O, Get_Symbol (+Element (Position)), As_String => True);
         Position := Next (Position);
         P (O, " ");
      end loop;
   end Print_Label_List;

   ----------------
   -- Print_List --
   ----------------

   procedure Print_List
     (State     : in out Printer_State'Class;
      List_Id   : Why_Node_List;
      Separator : String := ", ";
      Newline   : Boolean := False)
   is
      use Node_Lists;

      Nodes    : constant List := Get_List (List_Id);
      Position : Cursor := First (Nodes);
   begin
      while Position /= No_Element loop
         declare
            Node : constant Why_Node_Id := Element (Position);
         begin
            Traverse (State, Node);
         end;

         Position := Next (Position);

         if Position /= No_Element then
            P (O, Separator);
            if Newline then
               NL (O);
            end if;
         end if;
      end loop;
   end Print_List;

   ---------------------
   -- Sprint_Why_Node --
   ---------------------

   procedure Sprint_Why_Node (Node : Why_Node_Id; To : Output_Id := Stdout) is
      PS : Printer_State := (Control => Continue);
   begin
      O := To;
      Traverse (PS, +Node);
   end Sprint_Why_Node;

   ---------
   -- wpg --
   ---------

   procedure wpg (Node : Why_Node_Id) is
   begin
      Sprint_Why_Node (Node, Stdout);
      NL (Stdout);
   end wpg;

   ----------------------------------------
   -- Pre-operations and post-operations --
   ----------------------------------------

   --  Note: the following subprograms have been written from the stub
   --  generated by the xtree; the order of generation has been kept. That
   --  explains why these are not in alphabetical order.

   ----------------------
   -- Base_Type_Pre_Op --
   ----------------------

   procedure Base_Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Base_Type_Id)
   is
      pragma Unreferenced (State);
      Base_Type : constant EW_Type := Get_Base_Type (Node);
   begin
      if Base_Type = EW_Abstract then
         declare
            N : constant Node_Id := Get_Ada_Node (+Node);
         begin
            P (O, Capitalize_First (Full_Name (N)));
            P (O, ".");
            P (O, Short_Name (N));
         end;
      else
         P (O, Base_Type);
      end if;
   end Base_Type_Pre_Op;

   ---------------------
   -- Ref_Type_Pre_Op --
   ---------------------

   procedure Ref_Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Ref_Type_Id)
   is
      pragma Unreferenced (State);
      pragma Unreferenced (Node);
   begin
      P (O, "ref ");
   end Ref_Type_Pre_Op;

   --------------------
   -- Effects_Pre_Op --
   --------------------

   procedure Effects_Pre_Op
     (State : in out Printer_State;
      Node  : W_Effects_Id)
   is
      Reads  : constant W_Identifier_List := Get_Reads (Node);
      Writes : constant W_Identifier_List := Get_Writes (Node);
      Raises : constant W_Identifier_List := Get_Raises (Node);
   begin
      if not Is_Empty (+Reads) then
         P (O, "reads {");
         Print_List (State, +Reads, ", ");
         PL (O, " }");
      end if;

      if not Is_Empty (+Writes) then
         P (O, "writes {");
         Print_List (State, +Writes, ", ");
         PL (O, " }");
      end if;

      if not Is_Empty (+Raises) then
         P (O, "raises { ");
         Print_List (State, +Raises, ", ");
         PL (O, " }");
      end if;

      State.Control := Abandon_Children;
   end Effects_Pre_Op;

   -------------------
   -- Binder_Pre_Op --
   -------------------

   procedure Binder_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binder_Id)
   is
   begin
      Traverse (State, +Get_Name (Node));
      P (O, " : ");
      Traverse (State, +Get_Arg_Type (Node));

      State.Control := Abandon_Children;
   end Binder_Pre_Op;

   ------------------------
   -- Constr_Decl_Pre_Op --
   ------------------------

   procedure Constr_Decl_Pre_Op
      (State : in out Printer_State;
       Node : W_Constr_Decl_Id)
   is
      Args : constant W_Primitive_Type_List := Get_Arg_List (Node);
      Name : constant W_Identifier_Id := Get_Name (Node);
   begin
      P (O, "| ");
      Traverse (State, +Name);

      if not Is_Empty (+Args) then
         P (O, " (");
         Print_List (State, +Args, ", ");
         P (O, " )");
      end if;

      NL (O);
      State.Control := Abandon_Children;
   end Constr_Decl_Pre_Op;

   ------------------------------
   -- Record_Definition_Pre_Op --
   ------------------------------

   procedure Record_Definition_Pre_Op
      (State : in out Printer_State;
       Node : W_Record_Definition_Id)
   is
   begin
      P (O, "{ ");
      Print_List (State, +Get_Fields (Node), "; ");
      P (O, " }");
      State.Control := Abandon_Children;
   end Record_Definition_Pre_Op;

   ---------------------
   -- Triggers_Pre_Op --
   ---------------------

   procedure Triggers_Pre_Op
     (State : in out Printer_State;
      Node  : W_Triggers_Id)
   is
      Triggers : constant W_Trigger_List := Get_Triggers (Node);
   begin
      P (O, "[");
      Print_List (State, +Triggers, " | ");
      P (O, "]");
      State.Control := Abandon_Children;
   end Triggers_Pre_Op;

   --------------------
   -- Trigger_Pre_Op --
   --------------------

   procedure Trigger_Pre_Op
     (State : in out Printer_State;
      Node  : W_Trigger_Id)
   is
      Terms    : constant W_Expr_OList := Get_Terms (Node);
   begin
      Print_List (State, +Terms);
      State.Control := Abandon_Children;
   end Trigger_Pre_Op;

   -----------------------
   -- Match_Case_Pre_Op --
   -----------------------

   procedure Match_Case_Pre_Op
     (State : in out Printer_State;
      Node  : W_Match_Case_Id)
   is
   begin
      P (O, "| ");
      Traverse (State, +Get_Pattern (Node));
      P (O, " -> ");
      NL (O);
      Relative_Indent (O, 1);
      Traverse (State, +Get_Term (Node));
      Relative_Indent (O, -1);
      NL (O);
      State.Control := Abandon_Children;
   end Match_Case_Pre_Op;

   --------------------------
   -- Postcondition_Pre_Op --
   --------------------------

   procedure Postcondition_Pre_Op
     (State : in out Printer_State;
      Node  : W_Postcondition_Id)
   is
      Handlers : constant W_Exn_Condition_OList := Get_Handlers (Node);
   begin
      Traverse (State, +Get_Pred (Node));

      if not Is_Empty (+Handlers) then
         NL (O);
         Relative_Indent (O, 1);
         Print_List (State, +Handlers, "", Newline => True);
         Relative_Indent (O, -1);
      end if;

      State.Control := Abandon_Children;
   end Postcondition_Pre_Op;

   --------------------------
   -- Exn_Condition_Pre_Op --
   --------------------------

   procedure Exn_Condition_Pre_Op
     (State : in out Printer_State;
      Node  : W_Exn_Condition_Id)
   is
   begin
      P (O, "| ");
      Traverse (State, +Get_Exn_Case (Node));
      P (O, " => ");
      Traverse (State, +Get_Pred (Node));
      State.Control := Abandon_Children;
   end Exn_Condition_Pre_Op;

   -----------------------
   -- Loop_Annot_Pre_Op --
   -----------------------

   procedure Loop_Annot_Pre_Op
     (State : in out Printer_State;
      Node  : W_Loop_Annot_Id)
   is
      Invariant : constant W_Pred_OId := Get_Invariant (Node);
      Variant   : constant W_Wf_Arg_OId := Get_Variant (Node);
   begin
      if Invariant /= Why_Empty then
         P (O, "invariant ");
         PL (O, "{ ");
         Relative_Indent (O, 1);
         Traverse (State, +Invariant);
         NL (O);
         Relative_Indent (O, -1);
         P (O, " }");
      end if;

      if Variant /= Why_Empty then
         P (O, "variant ");
         Traverse (State, +Variant);
         NL (O);
      end if;

      State.Control := Abandon_Children;
   end Loop_Annot_Pre_Op;

   -------------------
   -- Wf_Arg_Pre_Op --
   -------------------

   procedure Wf_Arg_Pre_Op
     (State : in out Printer_State;
      Node  : W_Wf_Arg_Id)
   is
      For_Id : constant W_Identifier_OId := Get_For_Id (Node);
   begin
      Traverse (State, +Get_Def (Node));

      if For_Id /= Why_Empty then
         P (O, " for ");
         Traverse (State, +For_Id);
      end if;

      State.Control := Abandon_Children;
   end Wf_Arg_Pre_Op;

   --------------------
   -- Handler_Pre_Op --
   --------------------

   procedure Handler_Pre_Op
     (State : in out Printer_State;
      Node  : W_Handler_Id)
   is
      Arg : constant W_Prog_OId := Get_Arg (Node);
   begin
      Traverse (State, +Get_Name (Node));

      if Arg /= Why_Empty then
         P (O, " ");
         Traverse (State, +Arg);
      end if;

      P (O, " -> ");
      Traverse (State, +Get_Def (Node));
      State.Control := Abandon_Children;
   end Handler_Pre_Op;

   ------------------------------
   -- Universal_Quantif_Pre_Op --
   ------------------------------

   procedure Universal_Quantif_Pre_Op
     (State : in out Printer_State;
      Node  : W_Universal_Quantif_Id)
   is
      Variables       : constant W_Identifier_List := Get_Variables (Node);
      Var_Type        : constant W_Primitive_Type_Id := Get_Var_Type (Node);
      Triggers        : constant W_Triggers_OId := Get_Triggers (Node);
      Pred            : constant W_Pred_Id := Get_Pred (Node);
      Forall_Sequence : constant Boolean :=
                          Get_Kind (+Pred) = W_Universal_Quantif;
   begin
      P (O, "(forall ");
      Print_List (State, +Variables, " ");
      P (O, " ");
      Print_List (State, +Get_Labels (Node), " ");
      P (O, " : ");
      Traverse (State, +Var_Type);

      if Triggers /= Why_Empty then
         P (O, " ");
         Traverse (State, +Triggers);
      end if;

      PL (O, ".");

      if not Forall_Sequence then
         Relative_Indent (O, 1);
      end if;

      Traverse (State, +Pred);

      if not Forall_Sequence then
         Relative_Indent (O, -1);
      end if;
      P (O, ")");
      State.Control := Abandon_Children;
   end Universal_Quantif_Pre_Op;

   --------------------------------
   -- Existential_Quantif_Pre_Op --
   --------------------------------

   procedure Existential_Quantif_Pre_Op
     (State : in out Printer_State;
      Node  : W_Existential_Quantif_Id)
   is
      Variables       : constant W_Identifier_List := Get_Variables (Node);
      Var_Type        : constant W_Primitive_Type_Id := Get_Var_Type (Node);
      Pred            : constant W_Pred_Id := Get_Pred (Node);
      Exists_Sequence : constant Boolean :=
                          Get_Kind (+Pred) = W_Existential_Quantif;
   begin
      P (O, "exists ");
      Print_List (State, +Variables, " ");
      P (O, " ");
      Print_List (State, +Get_Labels (Node), " ");

      P (O, " : ");
      Traverse (State, +Var_Type);
      PL (O, ".");

      if not Exists_Sequence then
         Relative_Indent (O, 1);
      end if;

      Traverse (State, +Pred);

      if not Exists_Sequence then
         Relative_Indent (O, -1);
      end if;

      State.Control := Abandon_Children;
   end Existential_Quantif_Pre_Op;

   ----------------
   -- Not_Pre_Op --
   ----------------

   procedure Not_Pre_Op
     (State : in out Printer_State;
      Node  : W_Not_Id)
   is
      Pred : constant W_Expr_Id := +Not_Get_Right (+Node);
   begin
      P (O, "not ( ");
      Traverse (State, +Pred);
      P (O, " )");
      State.Control := Abandon_Children;
   end Not_Pre_Op;

   ---------------------
   -- Relation_Pre_Op --
   ---------------------

   procedure Relation_Pre_Op
     (State : in out Printer_State;
      Node  : W_Relation_Id)
   is
      Left   : constant W_Value_Id := Get_Left (Node);
      Op     : constant EW_Relation := Get_Op (Node);
      Right  : constant W_Value_Id := Get_Right (Node);
      Op2    : constant EW_Relation := Get_Op2 (Node);
      Right2 : constant W_Value_OId := Get_Right2 (Node);
   begin
      P (O, "( ");
      Traverse (State, +Left);
      P (O, " ");
      P (O, Op, Get_Op_Type (Node));
      P (O, " ");
      Traverse (State, +Right);

      if Op2 /= EW_None then
         P (O, " ");
         P (O, Op2, Get_Op_Type (Node));
         P (O, " ");
         Traverse (State, +Right2);
      end if;

      P (O, " )");
      State.Control := Abandon_Children;
   end Relation_Pre_Op;

   ------------------------
   -- Connection_Pre_Op --
   ------------------------

   procedure Connection_Pre_Op
     (State : in out Printer_State;
      Node  : W_Connection_Id)
   is
      Left       : constant W_Expr_Id := Get_Left (Node);
      Op         : constant EW_Connector := Get_Op (Node);
      Right      : constant W_Expr_Id := Get_Right (Node);
      More_Right : constant W_Expr_OList := Get_More_Right (Node);

   begin
      if not Is_Empty (+More_Right) then
         for E of Get_List (Why_Node_List (More_Right)) loop
            P (O, "( ");
         end loop;
      end if;

      P (O, "( ");
      Traverse (State, +Left);
      P (O, " ");
      P (O, Op);
      P (O, " ");
      Traverse (State, +Right);
      P (O, " )");

      if not Is_Empty (+More_Right) then
         for E of Get_List (Why_Node_List (More_Right)) loop
            P (O, " ");
            P (O, Op);
            P (O, " ");
            Traverse (State, +E);
            P (O, " )");
         end loop;
      end if;

      State.Control := Abandon_Children;
   end Connection_Pre_Op;

   -----------------------
   -- Identifier_Pre_Op --
   -----------------------

   procedure Identifier_Pre_Op
     (State : in out Printer_State;
      Node  : W_Identifier_Id)
   is
      Context : constant Name_Id := Get_Context (Node);
   begin
      if Context /= No_Name then
         P (O, Context);
         P (O, ".");
      end if;
      P (O, Get_Symbol (Node));
      State.Control := Abandon_Children;
   end Identifier_Pre_Op;

   -----------------------
   -- Tagged_Pre_Op --
   -----------------------

   procedure Tagged_Pre_Op
     (State : in out Printer_State;
      Node  : W_Tagged_Id)
   is
      Tag    : constant Name_Id := Get_Tag (Node);
   begin
      if Tag = No_Name then
         Traverse (State, +Get_Def (Node));

      elsif Get_Name_String (Tag) /= "" then
         P (O, "(at ");
         Traverse (State, +Get_Def (Node));
         P (O, " '");
         P (O, Tag);
         P (O, " )");
      else
         P (O, "(old ");
         Traverse (State, +Get_Def (Node));
         P (O, " )");
      end if;
      State.Control := Abandon_Children;
   end Tagged_Pre_Op;

   -----------------
   -- Call_Pre_Op --
   -----------------

   procedure Call_Pre_Op
     (State : in out Printer_State;
      Node  : W_Call_Id)
   is
      Name : constant W_Identifier_Id := Get_Name (Node);
      Args : constant W_Expr_OList := Get_Args (Node);

   begin
      --  The parentheses should only be needed when translating a term or
      --  predicate, but we use term nodes inside programs as a way to disable
      --  locally checks (say, to call the conversion function without range
      --  checks), so the argument of a term might be a program, which then
      --  needs being parenthesized.

      P (O, "(");
      case Get_Domain (+Node) is
         when EW_Term | EW_Pred =>
            Traverse (State, +Name);
            P (O, " ");
            Print_List (State, +Args, " ");

         when EW_Prog =>
            Traverse (State, +Name);

            if not Is_Empty (+Args) then
               P (O, "(");
               Print_List (State, +Args, ") (");
               P (O, ")");
            end if;
      end case;
      P (O, ")");

      State.Control := Abandon_Children;
   end Call_Pre_Op;

   -------------------
   -- Constr_Pre_Op --
   -------------------

   procedure Constr_Pre_Op
     (State : in out Printer_State;
      Node  : W_Constr_Id) is
   begin
      Traverse (State, +Get_Name (Node));
      P (O, "(");
      Print_List (State, +Get_Args (Node), ", ");
      P (O, ")");
      State.Control := Abandon_Children;
   end Constr_Pre_Op;

   --------------------
   -- Literal_Pre_Op --
   --------------------

   procedure Literal_Pre_Op
     (State : in out Printer_State;
      Node  : W_Literal_Id)
   is
      pragma Unreferenced (State);
   begin
      P (O, Get_Value (Node), Get_Domain (+Node));
   end Literal_Pre_Op;

   ------------------
   -- Elsif_Pre_Op --
   ------------------

   procedure Elsif_Pre_Op
     (State : in out Printer_State;
      Node  : W_Elsif_Id)
   is
      Condition : constant W_Expr_Id := Get_Condition (Node);
      Then_Part : constant W_Expr_Id := Get_Then_Part (Node);
   begin
      P (O, " else if (");
      Traverse (State, +Condition);
      PL (O, ") then (");
      Relative_Indent (O, 1);
      Traverse (State, +Then_Part);
      Relative_Indent (O, -1);
      P (O, ")");

      State.Control := Abandon_Children;
   end Elsif_Pre_Op;

   ------------------------
   -- Conditional_Pre_Op --
   ------------------------

   procedure Conditional_Pre_Op
     (State : in out Printer_State;
      Node  : W_Conditional_Id)
   is
      Condition   : constant W_Expr_Id := Get_Condition (Node);
      Then_Part   : constant W_Expr_Id := Get_Then_Part (Node);
      Elsif_Parts : constant W_Expr_OList := Get_Elsif_Parts (Node);
      Else_Part   : constant W_Expr_OId := Get_Else_Part (Node);
      Has_Else    : constant Boolean := Else_Part /= Why_Empty;
      Has_Elsif   : constant Boolean :=
                      (Has_Else
                        and then Get_Kind (+Else_Part) = W_Conditional);
   begin
      P (O, "(if (");
      Traverse (State, +Condition);

      PL (O, ") then (");
      Relative_Indent (O, 1);
      Traverse (State, +Then_Part);
      Relative_Indent (O, -1);
      P (O, ")");

      if not Is_Empty (+Elsif_Parts) then
         Traverse_List (State, +Elsif_Parts);
      end if;

      if Has_Else then
         P (O, " else (");

         if not Has_Elsif then
            NL (O);
            Relative_Indent (O, 1);
         end if;

         Traverse (State, +Else_Part);

         if not Has_Elsif then
            Relative_Indent (O, -1);
         end if;
         P (O, ")");
      else
         if Get_Domain (+Node) = EW_Prog then
            null;
         else
            P (O, " else true");
         end if;
      end if;
      P (O, ")");

      State.Control := Abandon_Children;
   end Conditional_Pre_Op;

   -----------------------------
   -- Integer_Constant_Pre_Op --
   -----------------------------

   procedure Integer_Constant_Pre_Op
     (State : in out Printer_State;
      Node  : W_Integer_Constant_Id)
   is
      pragma Unreferenced (State);
      Value : constant Uint := Get_Value (Node);
   begin
      if Value < Uint_0 then
         P (O, "( ");
         P (O, Value);
         P (O, " )");
      else
         P (O, Value);
      end if;
   end Integer_Constant_Pre_Op;

   --------------------------
   -- Real_Constant_Pre_Op --
   --------------------------

   procedure Real_Constant_Pre_Op
     (State : in out Printer_State;
      Node  : W_Real_Constant_Id)
   is
      pragma Unreferenced (State);
   begin
      P (O, "(");
      P (O, Get_Value (Node));
      P (O, ")");
   end Real_Constant_Pre_Op;

   -----------------
   -- Void_Pre_Op --
   -----------------

   procedure Void_Pre_Op
     (State : in out Printer_State;
      Node  : W_Void_Id)
   is
      pragma Unreferenced (State);
      pragma Unreferenced (Node);
   begin
      P (O, "()");
   end Void_Pre_Op;

   ----------------------
   -- Binary_Op_Pre_Op --
   ----------------------

   procedure Binary_Op_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binary_Op_Id)
   is
   begin
      P (O, "( ");
      Traverse (State, +Get_Left (Node));
      P (O, " ");
      P (O, Get_Op (Node), Get_Op_Type (Node));
      P (O, " ");
      Traverse (State, +Get_Right (Node));
      P (O, " )");
      State.Control := Abandon_Children;
   end Binary_Op_Pre_Op;

   ---------------------
   -- Unary_Op_Pre_Op --
   ---------------------

   procedure Unary_Op_Pre_Op
     (State : in out Printer_State;
      Node  : W_Unary_Op_Id)
   is
      Op     : constant EW_Unary_Op := Get_Op (Node);
   begin
      P (O, "( ");
      P (O, Op, Get_Op_Type (Node));
      P (O, " ");
      Traverse (State, +Get_Right (Node));
      P (O, " )");
      State.Control := Abandon_Children;
   end Unary_Op_Pre_Op;

   ------------------
   -- Deref_Pre_Op --
   ------------------

   procedure Deref_Pre_Op
     (State : in out Printer_State;
      Node  : W_Deref_Id)
   is
      pragma Unreferenced (State);
      pragma Unreferenced (Node);
   begin
      P (O, "!");
   end Deref_Pre_Op;

   ------------------
   -- Match_Pre_Op --
   ------------------

   procedure Match_Pre_Op
     (State : in out Printer_State;
      Node  : W_Match_Id)
   is
   begin
      P (O, "match ");
      Traverse (State, +Get_Term (Node));
      PL (O, " with");
      Relative_Indent (O, 1);
      Traverse_List (State, +Get_Branches (Node));
      Relative_Indent (O, -1);
      PL (O, "end");
      State.Control := Abandon_Children;
   end Match_Pre_Op;

   --------------------
   -- Binding_Pre_Op --
   --------------------

   procedure Binding_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binding_Id)
   is
      Name             : constant W_Identifier_Id := Get_Name (Node);
      Def              : constant W_Value_Id := Get_Def (Node);
      Context          : constant W_Expr_Id := Get_Context (Node);
      Binding_Sequence : constant Boolean := Get_Kind (+Context) = W_Binding;
   begin
      P (O, "(let ");
      Traverse (State, +Name);
      P (O, " = ");
      Traverse (State, +Def);
      PL (O, " in (");

      if not Binding_Sequence then
         Relative_Indent (O, 1);
      end if;

      Traverse (State, +Context);

      if not Binding_Sequence then
         Relative_Indent (O, -1);
      end if;

      PL (O, "))");

      State.Control := Abandon_Children;
   end Binding_Pre_Op;

   -------------------------
   -- Array_Access_Pre_Op --
   -------------------------

   procedure Array_Access_Pre_Op
     (State : in out Printer_State;
      Node  : W_Array_Access_Id)
   is
   begin
      Traverse (State, +Get_Name (Node));
      P (O, " [");
      Traverse (State, +Get_Index (Node));
      P (O, "]");
      State.Control := Abandon_Children;
   end Array_Access_Pre_Op;

   --------------------------
   -- Record_Access_Pre_Op --
   --------------------------

   procedure Record_Access_Pre_Op
     (State : in out Printer_State;
      Node  : W_Record_Access_Id)
   is
   begin
      Traverse (State, +Get_Name (Node));
      P (O, ".");
      Traverse (State, +Get_Field (Node));
      State.Control := Abandon_Children;
   end Record_Access_Pre_Op;

   --------------------------
   -- Record_Update_Pre_Op --
   --------------------------

   procedure Record_Update_Pre_Op
     (State : in out Printer_State;
      Node  : W_Record_Update_Id)
   is
   begin
      P (O, "{ ( ");
      Traverse (State, +Get_Name (Node));
      P (O, " ) with ");
      Print_List (State, +Get_Updates (Node), "; ");
      P (O, " }");
      State.Control := Abandon_Children;
   end Record_Update_Pre_Op;

   -----------------------------
   -- Record_Aggregate_Pre_Op --
   -----------------------------

   procedure Record_Aggregate_Pre_Op
     (State : in out Printer_State;
      Node  : W_Record_Aggregate_Id)
   is
   begin
      P (O, "{ ");
      Print_List (State, +Get_Associations (Node), "; ");
      P (O, " }");
      State.Control := Abandon_Children;
   end Record_Aggregate_Pre_Op;

   -----------------------------
   -- Field_Association_Pre_Op --
   -----------------------------

   procedure Field_Association_Pre_Op
     (State : in out Printer_State;
      Node  : W_Field_Association_Id)
   is
   begin
      Traverse (State, +Get_Field (Node));
      P (O, " = ");
      Traverse (State, +Get_Value (Node));
      State.Control := Abandon_Children;
   end Field_Association_Pre_Op;
   ---------------------
   -- Any_Expr_Pre_Op --
   ---------------------

   procedure Any_Expr_Pre_Op
     (State : in out Printer_State;
      Node  : W_Any_Expr_Id)
   is
      Res_Ty  : constant W_Simple_Value_Type_Id := Get_Return_Type (Node);
      Pre     : constant W_Pred_Id := Get_Pre (Node);
      Post    : constant W_Pred_Id := Get_Post (Node);
   begin
      P (O, "(any ");
      Traverse (State, +Res_Ty);
      NL (O);
      if Pre /= Why_Empty then
         P (O, "requires {");
         Traverse (State, +Pre);
         PL (O, "} ");
      end if;
      if Post /= Why_Empty then
         P (O, "ensures {");
         Traverse (State, +Post);
         PL (O, "} ");
      end if;
      P (O, ")");
      State.Control := Abandon_Children;
   end Any_Expr_Pre_Op;

   -----------------------
   -- Assignment_Pre_Op --
   -----------------------

   procedure Assignment_Pre_Op
     (State : in out Printer_State;
      Node  : W_Assignment_Id)
   is
   begin
      Traverse (State, +Get_Name (Node));
      P (O, " := ( ");
      Traverse (State, +Get_Value (Node));
      P (O, " )");
      State.Control := Abandon_Children;
   end Assignment_Pre_Op;

   -------------------------
   -- Array_Update_Pre_Op --
   -------------------------

   procedure Array_Update_Pre_Op
     (State : in out Printer_State;
      Node  : W_Array_Update_Id)
   is
   begin
      Traverse (State, +Get_Name (Node));
      P (O, " [");
      Traverse (State, +Get_Index (Node));
      P (O, "] := ");
      Traverse (State, +Get_Value (Node));
      State.Control := Abandon_Children;
   end Array_Update_Pre_Op;

   ------------------------
   -- Binding_Ref_Pre_Op --
   ------------------------

   procedure Binding_Ref_Pre_Op
     (State : in out Printer_State;
      Node  : W_Binding_Ref_Id)
   is
      Context          : constant W_Prog_Id := Get_Context (Node);
      Binding_Sequence : constant Boolean :=
                           Get_Kind (+Context) = W_Binding_Ref;
   begin
      P (O, "let ");
      Traverse (State, +Get_Name (Node));
      P (O, " ");
      Print_List (State, +Get_Labels (Node), " ");
      P (O, " = ref (");
      Traverse (State, +Get_Def (Node));
      PL (O, ") in ");

      if not Binding_Sequence then
         Relative_Indent (O, 1);
      end if;

      Traverse (State, +Context);

      if not Binding_Sequence then
         Relative_Indent (O, -1);
      end if;

      State.Control := Abandon_Children;
   end Binding_Ref_Pre_Op;

   -----------------------
   -- While_Loop_Pre_Op --
   -----------------------

   procedure While_Loop_Pre_Op
     (State : in out Printer_State;
      Node  : W_While_Loop_Id)
   is
      Condition    : constant W_Prog_Id := Get_Condition (Node);
      Annotation   : constant W_Loop_Annot_OId := Get_Annotation (Node);
      Loop_Content : constant W_Prog_Id := Get_Loop_Content (Node);
   begin
      P (O, "while ");
      Traverse (State, +Condition);
      PL (O, " do");
      Relative_Indent (O, 1);

      if Annotation /= Why_Empty then
         Traverse (State, +Annotation);
         NL (O);
      end if;

      Traverse (State, +Loop_Content);
      Relative_Indent (O, -1);
      NL (O);
      P (O, "done");
      State.Control := Abandon_Children;
   end While_Loop_Pre_Op;

   -------------------------------
   -- Statement_Sequence_Pre_Op --
   -------------------------------

   procedure Statement_Sequence_Pre_Op
     (State : in out Printer_State;
      Node  : W_Statement_Sequence_Id)
   is
   begin
      P (O, "( ");
      Print_List (State, +Get_Statements (Node), ";", Newline => True);
      P (O, " )");
      State.Control := Abandon_Children;
   end Statement_Sequence_Pre_Op;

   --------------------------
   -- Abstract_Expr_Pre_Op --
   --------------------------

   procedure Abstract_Expr_Pre_Op
     (State : in out Printer_State;
      Node  : W_Abstract_Expr_Id)
   is
   begin
      P (O, "abstract ");
      Traverse (State, +Get_Expr (Node));
      P (O, " ensures {");
      Traverse (State, +Get_Post (Node));
      P (O, "}");
      State.Control := Abandon_Children;
   end Abstract_Expr_Pre_Op;

   ------------------
   -- Label_Pre_Op --
   ------------------

   procedure Label_Pre_Op
     (State : in out Printer_State;
      Node  : W_Label_Id)
   is
      use Node_Lists;

      L      : constant List := Get_List (+Get_Labels (Node));
      Non_Empty : constant Boolean := not (L.Is_Empty);
   begin
      if Non_Empty then
         P (O, "( ");
      end if;
      Print_Label_List (State, +Get_Labels (Node));
      Traverse (State, +Get_Def (Node));
      if Non_Empty then
         P (O, " )");
      end if;
      State.Control := Abandon_Children;
   end Label_Pre_Op;

   -------------------
   -- Assert_Pre_Op --
   -------------------

   procedure Assert_Pre_Op
     (State : in out Printer_State;
      Node  : W_Assert_Id)
   is
      pragma Unreferenced (State);
      pragma Unreferenced (Node);
   begin
      P (O, "assert { ");
   end Assert_Pre_Op;

   --------------------
   -- Assert_Post_Op --
   --------------------

   procedure Assert_Post_Op
     (State : in out Printer_State;
      Node  : W_Assert_Id)
   is
      pragma Unreferenced (State);
      pragma Unreferenced (Node);
   begin
      P (O, " }");
   end Assert_Post_Op;

   ------------------
   -- Raise_Pre_Op --
   ------------------

   procedure Raise_Pre_Op
     (State : in out Printer_State;
      Node  : W_Raise_Id)
   is
      Exn_Type : constant W_Simple_Value_Type_OId := Get_Exn_Type (Node);
   begin
      P (O, "raise ");

      Traverse (State, +Get_Name (Node));

      if Exn_Type /= Why_Empty then
         P (O, " : ");
         Traverse (State, +Exn_Type);
      end if;

      State.Control := Abandon_Children;
   end Raise_Pre_Op;

   ----------------------
   -- Try_Block_Pre_Op --
   ----------------------

   procedure Try_Block_Pre_Op
     (State : in out Printer_State;
      Node  : W_Try_Block_Id)
   is
   begin
      PL (O, "try");
      Relative_Indent (O, 1);
      Traverse (State, +Get_Prog (Node));
      Relative_Indent (O, -1);
      NL (O);
      PL (O, "with");
      Relative_Indent (O, 1);
      Print_List (State, +Get_Handler (Node), ", ", Newline => True);
      Relative_Indent (O, -1);
      NL (O);
      P (O, "end");
      State.Control := Abandon_Children;
   end Try_Block_Pre_Op;

   ----------------------
   -- Tag_Intro_Pre_Op --
   ----------------------

   procedure Tag_Intro_Pre_Op
     (State : in out Printer_State;
      Node  : W_Tag_Intro_Id)
   is
   begin
      P (O, "( '");
      P (O, +Get_Tag (Node));
      P (O, " : ");
      Traverse (State, +Get_Prog (Node));
      P (O, " )");
      State.Control := Abandon_Children;
   end Tag_Intro_Pre_Op;

   -----------------------------
   -- Unreachable_Code_Pre_Op --
   -----------------------------

   procedure Unreachable_Code_Pre_Op
     (State : in out Printer_State;
      Node  : W_Unreachable_Code_Id)
   is
      Exn_Type : constant W_Simple_Value_Type_OId :=
                   Get_Exn_Type (Node);
   begin
      P (O, "absurd");

      if Exn_Type /= Why_Empty then
         P (O, " : ");
         Traverse (State, +Exn_Type);
      end if;

      State.Control := Abandon_Children;
   end Unreachable_Code_Pre_Op;

   --------------------------
   -- Function_Decl_Pre_Op --
   --------------------------

   procedure Function_Decl_Pre_Op
     (State : in out Printer_State;
      Node  : W_Function_Decl_Id)
   is
      Name        : constant W_Identifier_Id := Get_Name (Node);
      Return_Type : constant W_Simple_Value_Type_Id := Get_Return_Type (Node);
      Binders     : constant W_Binder_OList := Get_Binders (Node);

   begin
      case Get_Domain (+Node) is
         when EW_Term =>
            P (O, "function ");

            Traverse (State, +Name);

            P (O, " ");
            Print_List (State, +Get_Labels (Node), " ");

            NL (O);
            Relative_Indent (O, 1);

            if not Is_Empty (+Binders) then
               P (O, " (");
               Print_List (State, +Binders, ") (");
               P (O, ") ");
            end if;
            P (O, " :");
            Traverse (State, +Return_Type);

            Relative_Indent (O, -1);
            NL (O);

         when EW_Prog =>
            P (O, "val ");

            Traverse (State, +Name);
            Relative_Indent (O, 1);
            NL (O);
            declare
               Pre         : constant W_Pred_Id := Get_Pre (Node);
               Effects     : constant W_Effects_Id := Get_Effects (Node);
               Post        : constant W_Pred_Id := Get_Post (Node);
            begin
               if not Is_Empty (+Binders) then
                  P (O, " (");
                  Print_List (State, +Binders, ") (");
                  P (O, ") ");
               end if;
               P (O, " :");
               Traverse (State, +Return_Type);
               NL (O);
               if Pre /= Why_Empty then
                  P (O, "requires { ");
                  Traverse (State, +Pre);
                  P (O, " }");
                  NL (O);
               end if;
               if Post /= Why_Empty then
                  P (O, "ensures { ");
                  Traverse (State, +Post);
                  P (O, " }");
                  NL (O);
               end if;
               if Effects /= Why_Empty then
                  Traverse (State, +Effects);
                  NL (O);
               end if;
               Relative_Indent (O, -1);
            end;

         when EW_Pred =>
            P (O, "predicate ");

            Traverse (State, +Name);

            NL (O);
            Relative_Indent (O, 1);

            if not Is_Empty (+Binders) then
               P (O, " (");
               Print_List (State, +Binders, ") (");
               P (O, ") ");
            end if;

            Relative_Indent (O, -1);
            NL (O);
      end case;

      State.Control := Abandon_Children;
   end Function_Decl_Pre_Op;

   -------------------------
   -- Function_Def_Pre_Op --
   -------------------------

   procedure Function_Def_Pre_Op
     (State : in out Printer_State;
      Node  : W_Function_Def_Id)
   is
      Spec        : constant W_Function_Decl_Id := Get_Spec (Node);
      Def         : constant W_Expr_Id := Get_Def (Node);
      Name        : constant W_Identifier_Id := Get_Name (Spec);
      Binders     : constant W_Binder_OList := Get_Binders (Spec);
      Return_Type : constant W_Simple_Value_Type_OId := Get_Return_Type (Spec);
      Pre         : constant W_Pred_OId := Get_Pre (Spec);
      Post        : constant W_Pred_OId := Get_Post (Spec);
   begin
      case Get_Domain (+Node) is
         when EW_Pred =>
            P (O, "predicate ");
            Traverse (State, +Name);

            P (O, " ");
            Print_Label_List (State, +Get_Labels (Node));

            P (O, " (");
            Print_List (State, +Binders, ") (");
            PL (O, ") =");

            Relative_Indent (O, 1);
            Traverse (State, +Def);
            Relative_Indent (O, -1);
            NL (O);

         when EW_Term =>
            P (O, "function ");
            Traverse (State, +Name);

            P (O, " ");
            Print_Label_List (State, +Get_Labels (Node));

            if not Is_Empty (+Binders) then
               P (O, " (");
               Print_List (State, +Binders, ") (");
               P (O, ")");
            end if;
            P (O, " : ");

            Traverse (State, +Return_Type);
            PL (O, " =");
            Relative_Indent (O, 1);
            Traverse (State, +Def);
            Relative_Indent (O, -1);
            NL (O);

         when EW_Prog =>
            P (O, "let ");
            Traverse (State, +Name);
            P (O, " ");
            Print_Label_List (State, +Get_Labels (Node));

            if not Is_Empty (+Binders) then
               P (O, " (");
               Print_List (State, +Binders, ") (");
               PL (O, ") ");
            end if;

            if Pre /= Why_Empty then
               P (O, "requires { ");
               Traverse (State, +Pre);
               PL (O, " }");
            end if;
            if Post /= Why_Empty then
               P (O, "ensures { ");
               Traverse (State, +Post);
               PL (O, " }");
            end if;
            PL (O, " = ");
            Relative_Indent (O, 1);
            Traverse (State, +Def);
            Relative_Indent (O, -1);
            NL (O);
      end case;

      State.Control := Abandon_Children;
   end Function_Def_Pre_Op;

   ------------------
   -- Axiom_Pre_Op --
   ------------------

   procedure Axiom_Pre_Op
     (State : in out Printer_State;
      Node  : W_Axiom_Id)
   is
   begin
      P (O, "axiom ");
      Traverse (State, +Get_Name (Node));
      PL (O, " :");
      Relative_Indent (O, 1);
      Traverse (State, +Get_Def (Node));
      Relative_Indent (O, -1);
      NL (O);
      State.Control := Abandon_Children;
   end Axiom_Pre_Op;

   -----------------
   -- Goal_Pre_Op --
   -----------------

   procedure Goal_Pre_Op
     (State : in out Printer_State;
      Node  : W_Goal_Id)
   is
   begin
      P (O, "goal ");
      Traverse (State, +Get_Name (Node));
      PL (O, " :");
      Relative_Indent (O, 1);
      Traverse (State, +Get_Def (Node));
      Relative_Indent (O, -1);
      NL (O);
      State.Control := Abandon_Children;
   end Goal_Pre_Op;

   -----------------
   -- Type_Pre_Op --
   -----------------

   procedure Type_Pre_Op
     (State : in out Printer_State;
      Node  : W_Type_Id)
   is
      use Node_Lists;

      Args       : constant List := Get_List (+Get_Args (Node));
      Nb_Args    : constant Count_Type := Length (Args);
      Position   : Cursor := First (Args);
      Name       : constant W_Identifier_Id := Get_Name (Node);
      Definition : constant W_Type_Definition_Id := Get_Definition (Node);
   begin
      P (O, "type ");

      Traverse (State, +Name);

      P (O, " ");
      Print_List (State, +Get_Labels (Node), " ");

      if Nb_Args > 1 then
         P (O, " (");
      end if;

      if Nb_Args > 0 then
         P (O, " ");
      end if;

      while Position /= No_Element loop
         P (O, "'");

         declare
            Param : constant Why_Node_Id := Element (Position);
         begin
            Traverse (State, Param);
         end;

         Position := Next (Position);

         if Position /= No_Element then
            P (O, ", ");
         end if;
      end loop;

      if Nb_Args > 1 then
         P (O, ")");
      end if;

      if Definition /= Why_Empty then
         P (O, " = ");
         NL (O);
         Relative_Indent (O, 1);
         Traverse (State, +Definition);
         Relative_Indent (O, -1);
      end if;

      NL (O);
      State.Control := Abandon_Children;
   end Type_Pre_Op;

   -----------------------------------
   -- Global_Ref_Declaration_Pre_Op --
   -----------------------------------

   procedure Global_Ref_Declaration_Pre_Op
     (State : in out Printer_State;
      Node  : W_Global_Ref_Declaration_Id)
   is
   begin
      P (O, "val ");
      Traverse (State, +Get_Name (Node));

      P (O, " ");
      Print_List (State, +Get_Labels (Node), " ");

      P (O, " : ref ");
      Traverse (State, +Get_Ref_Type (Node));
      NL (O);
      State.Control := Abandon_Children;
   end Global_Ref_Declaration_Pre_Op;

   ----------------------------------
   -- Exception_Declaration_Pre_Op --
   ----------------------------------

   procedure Exception_Declaration_Pre_Op
     (State : in out Printer_State;
      Node  : W_Exception_Declaration_Id)
   is
      Arg : constant W_Primitive_Type_OId := Get_Arg (Node);
   begin
      P (O, "exception ");
      Traverse (State, +Get_Name (Node));

      if Arg /= Why_Empty then
         P (O, "of ");
         Traverse (State, +Arg);
      end if;
      NL (O);

      State.Control := Abandon_Children;
   end Exception_Declaration_Pre_Op;

   --------------------------------
   -- Include_Declaration_Pre_Op --
   --------------------------------

   procedure Include_Declaration_Pre_Op
     (State : in out Printer_State;
      Node  : W_Include_Declaration_Id)
   is
      File : constant W_Identifier_OId := Get_File (Node);
   begin
      P (O, "use ");
      P (O, Get_Use_Kind (Node));
      P (O, " ");
      if File /= Why_Empty then
         P (O, """");
         Traverse (State, +File);
         P (O, """.");
      end if;
      Traverse (State, +Get_T_Name (Node));
      NL (O);
      State.Control := Abandon_Children;
   end Include_Declaration_Pre_Op;

   ------------------------------
   -- Clone_Declaration_Pre_Op --
   ------------------------------

   procedure Clone_Declaration_Pre_Op
      (State : in out Printer_State;
       Node  : W_Clone_Declaration_Id)
   is
      As_Name    : constant W_Identifier_OId := +Get_As_Name (Node);
      Subst_List : constant W_Clone_Substitution_OList :=
                        +Get_Substitutions (Node);
   begin
      P (O, "clone ");
      P (O, Get_Clone_Kind (Node));
      P (O, " ");
      Traverse (State, +Get_Origin (Node));
      if As_Name /= Why_Empty then
         P (O, " as ");
         Traverse (State, +As_Name);
      end if;
      if not Is_Empty (+Subst_List) then
         P (O, " with");
         NL (O);
         Print_List (State, +Subst_List, ", ", Newline => True);
      end if;
      NL (O);
      State.Control := Abandon_Children;
   end Clone_Declaration_Pre_Op;

   -------------------------------
   -- Clone_Substitution_Pre_Op --
   -------------------------------

   procedure Clone_Substitution_Pre_Op
      (State : in out Printer_State;
       Node  : W_Clone_Substitution_Id)
   is
   begin
      P (O, Get_Kind (Node));
      P (O, " ");
      Traverse (State, +Get_Orig_Name (Node));
      P (O, " = ");
      Traverse (State, +Get_Image (Node));
      State.Control := Abandon_Children;
   end Clone_Substitution_Pre_Op;

   -------------------------------
   -- Theory_Declaration_Pre_Op --
   -------------------------------

   procedure Theory_Declaration_Pre_Op
     (State : in out Printer_State;
      Node  : W_Theory_Declaration_Id)
   is
      Kind : constant EW_Theory_Type := Get_Kind (Node);
   begin
      P (O, "(* ");
      Traverse (State, +Get_Comment (Node));
      PL (O, " *)");
      P (O, Kind, False);
      P (O, " ");
      Traverse (State, +Get_Name (Node));
      NL (O);
      Relative_Indent (O, 1);
      Print_List (State, +Get_Includes (Node), "", Newline => False);
      NL (O);
      Print_List (State, +Get_Declarations (Node), "", Newline => True);
      Relative_Indent (O, -1);
      PL (O, "end");
      State.Control := Abandon_Children;
   end Theory_Declaration_Pre_Op;

   -------------------------------
   -- Custom_Declaration_Pre_Op --
   -------------------------------

   procedure Custom_Declaration_Pre_Op
     (State : in out Printer_State;
      Node  : W_Custom_Declaration_Id)
   is
      use GNAT.Regpat;

      function Get_Whole_File return String;
      --  Return whole contents of file associated with Node

      function Get_Regexp return String;
      --  ???

      procedure Apply_Subst (Text : String; Matches : Match_Array);
      --  ???

      function Locate_File return String;
      --  Return name of file associated with Node

      -----------------
      -- Locate_File --
      -----------------

      function Locate_File return String is
         use Ada.Directories;

         Dir : String_Access := Locate_Exec_On_Path (Exec_Name => "gnatprove");
      begin
         if Dir = null then
            Error_Msg_N
              ("cannot locate associated theory file", Get_Ada_Node (+Node));
            return "";
         end if;

         declare
            File_Name : constant String :=
              Get_Name_String (Get_File_Name (Node));
            From_Command : constant String :=
              Compose (Compose (Compose (Compose (Containing_Directory
                       (Containing_Directory (Dir.all)), "share"),
                       "spark"), "theories"), File_Name);

         begin
            Free (Dir);

            if Is_Readable_File (From_Command) then
               return From_Command;
            else
               Name_Len := From_Command'Length;
               Name_Buffer (1 .. Name_Len) := From_Command;
               Error_Msg_Name_1 := Name_Enter;
               Error_Msg_N
                 ("cannot read theory file %%", Get_Ada_Node (+Node));
               return "";
            end if;
         end;
      end Locate_File;

      --------------------
      -- Get_Whole_File --
      --------------------

      function Get_Whole_File return String is
         File_Name : constant String  := Locate_File;
      begin
         if File_Name = "" then
            return "";
         end if;

         declare
            File_Size : constant Natural :=
              Natural (Ada.Directories.Size (File_Name));

            subtype File_String    is String (1 .. File_Size);
            package File_String_IO is new Ada.Direct_IO (File_String);

            File     : File_String_IO.File_Type;
            Contents : File_String;

         begin
            File_String_IO.Open (File, Mode => File_String_IO.In_File,
                                 Name => File_Name);
            File_String_IO.Read  (File, Item => Contents);
            File_String_IO.Close (File);
            return Contents;
         end;
      end Get_Whole_File;

      ----------------
      -- Get_Regexp --
      ----------------

      function Get_Regexp return String is
         use Ada.Strings.Unbounded;
         use Node_Lists;

         Nodes    : constant List := Get_List (+Get_Subst (Node));
         Position : Cursor := First (Nodes);
         Result   : Unbounded_String := Null_Unbounded_String;

      begin
         while Position /= No_Element loop
            declare
               Node : constant W_Custom_Substitution_Id :=
                 W_Custom_Substitution_Id (Element (Position));
            begin
               Result := Result & Get_Name_String (Get_From (Node));
            end;

            Position := Next (Position);

            if Position /= No_Element then
               Result := Result & "|";
            end if;
         end loop;

         return To_String (Result);
      end Get_Regexp;

      -----------------
      -- Apply_Subst --
      -----------------

      procedure Apply_Subst (Text : String; Matches : Match_Array) is
         use Node_Lists;

         Nodes    : constant List := Get_List (+Get_Subst (Node));
         Position : Cursor := First (Nodes);
         Interm_Matches : Match_Array (0 .. 0);

      begin
         while Position /= No_Element loop
            declare
               Node : constant W_Custom_Substitution_Id :=
                 W_Custom_Substitution_Id (Element (Position));
            begin
               Match (Compile (Get_Name_String (Get_From (Node))), Text,
                      Interm_Matches, Matches (0).First);

               if Interm_Matches (0) /= No_Match
                 and then Interm_Matches (0).Last = Matches (0).Last
               then
                  Traverse (State, +Get_To (Node));
                  return;
               end if;
            end;

            Next (Position);
         end loop;

         raise Program_Error;
      end Apply_Subst;

      Text : constant String := Get_Whole_File;

   begin
      NL (O);

      if Node_Lists.Is_Empty (Get_List (+Get_Subst (Node))) then
         P (O, Text);
      else
         declare
            Regexp  : constant Pattern_Matcher := Compile (Get_Regexp);
            Matches : Match_Array (0 .. 0);
            Current : Natural := Text'First;
         begin
            loop
               Match (Regexp, Text, Matches, Current);
               exit when Matches (0) = No_Match;
               P (O, Text (Current .. Matches (0).First - 1));
               Apply_Subst (Text, Matches);
               Current := Matches (0).Last + 1;
            end loop;

            P (O, Text (Current .. Text'Last));
         end;
      end if;

      NL (O);
      State.Control := Abandon_Children;
   end Custom_Declaration_Pre_Op;

   -----------------
   -- File_Pre_Op --
   -----------------

   procedure File_Pre_Op
     (State : in out Printer_State;
      Node  : W_File_Id)
   is
   begin
      Print_List (State, +Get_Theories (Node), "", Newline => True);
      State.Control := Abandon_Children;
   end File_Pre_Op;

end Why.Atree.Sprint;
