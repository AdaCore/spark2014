------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                     W H Y - A T R E E - S P R I N T                      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2014, AdaCore                   --
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
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Modules;   use Why.Atree.Modules;
with Why.Ids;             use Why.Ids;
with Why.Images;          use Why.Images;
with Why.Conversions;     use Why.Conversions;

with Ada.Directories;
with Ada.Direct_IO;
with GNAT.Regpat;
with GNAT.OS_Lib; use GNAT.OS_Lib;
with Ada.Strings.Unbounded;

with Gnat2Why_Args;

package body Why.Atree.Sprint is

   O : Output_Id := Stdout;

   procedure Print_Node (N : Why_Node_Id);
   --  printing function for any node, calls the other functions in this
   --  package as needed

   procedure Print_List
     (List_Id   : Why_Node_List;
      Separator : String := ", ";
      Newline   : Boolean := False);
   --  Print a node list on current output, separating each element
   --  by a given separator, optionally followed by a new line.

   procedure Print_Module_Id
     (Node      : W_Module_Id;
      With_File : Boolean := False);

   --  printing subprograms for each node

   procedure Print_Abstract_Expr (Node : W_Abstract_Expr_Id);
   procedure Print_Any_Expr (Node : W_Any_Expr_Id);
   procedure Print_Assert (Node : W_Assert_Id);
   procedure Print_Assignment (Node : W_Assignment_Id);
   procedure Print_Axiom (Node : W_Axiom_Id);
   procedure Print_Binary_Op (Node : W_Binary_Op_Id);
   procedure Print_Binder (Node : W_Binder_Id);
   procedure Print_Binding (Node : W_Binding_Id);
   procedure Print_Binding_Ref (Node : W_Binding_Ref_Id);
   procedure Print_Call (Node : W_Call_Id);
   procedure Print_Clone_Declaration (Node : W_Clone_Declaration_Id);
   procedure Print_Clone_Substitution (Node : W_Clone_Substitution_Id);
   procedure Print_Comment (Node : W_Comment_Id);
   procedure Print_Conditional (Node : W_Conditional_Id);
   procedure Print_Connection (Node : W_Connection_Id);
   procedure Print_Custom_Declaration (Node : W_Custom_Declaration_Id);
   procedure Print_Deref (Node : W_Deref_Id);
   procedure Print_Effects (Node : W_Effects_Id);
   procedure Print_Elsif (Node : W_Elsif_Id);
   procedure Print_Exception_Declaration (Node : W_Exception_Declaration_Id);
   procedure Print_Existential_Quantif (Node : W_Existential_Quantif_Id);
   procedure Print_Exn_Condition (Node : W_Exn_Condition_Id);
   procedure Print_Field_Association (Node : W_Field_Association_Id);
   procedure Print_File (Node : W_File_Id);
   procedure Print_Fixed_Constant (Node : W_Fixed_Constant_Id);
   procedure Print_Function_Decl (Node : W_Function_Decl_Id);
   procedure Print_Global_Ref_Declaration (Node : W_Global_Ref_Declaration_Id);
   procedure Print_Goal (Node : W_Goal_Id);
   procedure Print_Handler (Node : W_Handler_Id);
   procedure Print_Identifier (Node : W_Identifier_Id);
   procedure Print_Include_Declaration (Node : W_Include_Declaration_Id);
   procedure Print_Integer_Constant (Node : W_Integer_Constant_Id);
   procedure Print_Label (Node : W_Label_Id);
   procedure Print_Literal (Node : W_Literal_Id);
   procedure Print_Loop_Annot (Node : W_Loop_Annot_Id);
   procedure Print_Name (Node : W_Name_Id);
   procedure Print_Not (Node : W_Not_Id);
   procedure Print_Postcondition (Node : W_Postcondition_Id);
   procedure Print_Raise (Node : W_Raise_Id);
   procedure Print_Real_Constant (Node : W_Real_Constant_Id);
   procedure Print_Record_Access (Node : W_Record_Access_Id);
   procedure Print_Record_Aggregate (Node : W_Record_Aggregate_Id);
   procedure Print_Record_Definition (Node : W_Record_Definition_Id);
   procedure Print_Record_Update (Node : W_Record_Update_Id);
   procedure Print_Relation (Node : W_Relation_Id);
   procedure Print_Statement_Sequence (Node : W_Statement_Sequence_Id);
   procedure Print_Tagged (Node : W_Tagged_Id);
   procedure Print_Theory_Declaration (Node : W_Theory_Declaration_Id);
   procedure Print_Transparent_Type_Definition
      (N : W_Transparent_Type_Definition_Id);
   procedure Print_Trigger (Node : W_Trigger_Id);
   procedure Print_Triggers (Node : W_Triggers_Id);
   procedure Print_Try_Block (Node : W_Try_Block_Id);
   procedure Print_Type (Node : W_Type_Id);
   procedure Print_Type_Decl (Node : W_Type_Decl_Id);
   procedure Print_Unary_Op (Node : W_Unary_Op_Id);
   procedure Print_Universal_Quantif (Node : W_Universal_Quantif_Id);
   procedure Print_Void (Node : W_Void_Id);
   procedure Print_While_Loop (Node : W_While_Loop_Id);

   --------------------------
   -- Print_Abstract_Expr --
   --------------------------

   procedure Print_Abstract_Expr (Node : W_Abstract_Expr_Id) is
   begin
      P (O, "abstract ensures {");
      Print_Node (+Get_Post (Node));
      P (O, "}");
      Print_Node (+Get_Expr (Node));
      P (O, " end ");
   end Print_Abstract_Expr;

   ---------------------
   -- Print_Any_Expr --
   ---------------------

   procedure Print_Any_Expr (Node : W_Any_Expr_Id) is
      Res_Ty  : constant W_Type_Id := Get_Return_Type (Node);
      Effects : constant W_Effects_Id := Get_Effects (Node);
      Pre     : constant W_Pred_Id := Get_Pre (Node);
      Post    : constant W_Pred_Id := Get_Post (Node);
   begin
      P (O, "(any ");
      Print_Node (+Res_Ty);
      NL (O);
      if Pre /= Why_Empty then
         P (O, "requires {");
         Print_Node (+Pre);
         PL (O, "} ");
      end if;
      if Post /= Why_Empty then
         P (O, "ensures {");
         Print_Node (+Post);
         PL (O, "} ");
      end if;
      if Effects /= Why_Empty then
         Print_Node (+Effects);
         NL (O);
      end if;
      P (O, ")");
   end Print_Any_Expr;

   -------------------
   -- Print_Assert --
   -------------------

   procedure Print_Assert (Node : W_Assert_Id) is
   begin
      P (O, Get_Assert_Kind (Node));
      P (O, " { ");
      Print_Node (+Get_Pred (Node));
      P (O, " }");
   end Print_Assert;

   -----------------------
   -- Print_Assignment --
   -----------------------

   procedure Print_Assignment (Node : W_Assignment_Id) is
   begin
      Print_Node (+Get_Name (Node));
      P (O, " := ( ");
      Print_Node (+Get_Value (Node));
      P (O, " )");
   end Print_Assignment;

   ------------------
   -- Print_Axiom --
   ------------------

   procedure Print_Axiom (Node : W_Axiom_Id) is
   begin
      P (O, "axiom ");
      P (O, Get_Name (Node));
      PL (O, " :");
      Relative_Indent (O, 1);
      Print_Node (+Get_Def (Node));
      Relative_Indent (O, -1);
      NL (O);
   end Print_Axiom;

   ----------------------
   -- Print_Binary_Op --
   ----------------------

   procedure Print_Binary_Op (Node : W_Binary_Op_Id) is
   begin
      P (O, "( ");
      Print_Node (+Get_Left (Node));
      P (O, " ");
      P (O, Get_Op (Node), Get_Op_Type (Node));
      P (O, " ");
      Print_Node (+Get_Right (Node));
      P (O, " )");
   end Print_Binary_Op;

   -------------------
   -- Print_Binder --
   -------------------

   procedure Print_Binder (Node  : W_Binder_Id)
   is
   begin
      Print_Node (+Get_Name (Node));
      P (O, " : ");
      Print_Node (+Get_Arg_Type (Node));
   end Print_Binder;

   --------------------
   -- Print_Binding --
   --------------------

   procedure Print_Binding (Node : W_Binding_Id) is
      Name             : constant W_Identifier_Id := Get_Name (Node);
      Def              : constant W_Expr_Id := Get_Def (Node);
      Context          : constant W_Expr_Id := Get_Context (Node);
      Binding_Sequence : constant Boolean := Get_Kind (+Context) = W_Binding;
   begin
      P (O, "(let ");
      Print_Node (+Name);
      P (O, " = ");
      Print_Node (+Def);
      PL (O, " in (");

      if not Binding_Sequence then
         Relative_Indent (O, 1);
      end if;

      Print_Node (+Context);

      if not Binding_Sequence then
         Relative_Indent (O, -1);
      end if;

      PL (O, "))");
   end Print_Binding;

   ------------------------
   -- Print_Binding_Ref --
   ------------------------

   procedure Print_Binding_Ref (Node : W_Binding_Ref_Id) is
      Context          : constant W_Prog_Id := Get_Context (Node);
      Binding_Sequence : constant Boolean :=
        Get_Kind (+Context) = W_Binding_Ref;
   begin
      P (O, "let ");
      Print_Node (+Get_Name (Node));
      P (O, " = ref (");
      Print_Node (+Get_Def (Node));
      PL (O, ") in ");

      if not Binding_Sequence then
         Relative_Indent (O, 1);
      end if;

      Print_Node (+Context);

      if not Binding_Sequence then
         Relative_Indent (O, -1);
      end if;
   end Print_Binding_Ref;

   -----------------
   -- Print_Call --
   -----------------

   procedure Print_Call (Node : W_Call_Id) is
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
            Print_Node (+Name);
            P (O, " ");
            Print_List (+Args, " ");

         when EW_Prog =>
            Print_Node (+Name);

            if not Is_Empty (+Args) then
               P (O, "(");
               Print_List (+Args, ") (");
               P (O, ")");
            end if;
      end case;
      P (O, ")");
   end Print_Call;

   ------------------------------
   -- Print_Clone_Declaration --
   ------------------------------

   procedure Print_Clone_Declaration (Node : W_Clone_Declaration_Id) is
      As_Name    : constant Name_Id := Get_As_Name (Node);
      Subst_List : constant W_Clone_Substitution_OList :=
        +Get_Substitutions (Node);
   begin
      P (O, "clone ");
      P (O, Get_Clone_Kind (Node));
      P (O, " ");
      Print_Module_Id (Get_Origin (Node), With_File => True);
      if As_Name /= No_Name then
         P (O, " as ");
         P (O, As_Name);
      end if;
      if not Is_Empty (+Subst_List) then
         P (O, " with");
         NL (O);
         Print_List (+Subst_List, ", ", Newline => True);
      end if;
      NL (O);
   end Print_Clone_Declaration;

   -------------------------------
   -- Print_Clone_Substitution --
   -------------------------------

   procedure Print_Clone_Substitution (Node : W_Clone_Substitution_Id) is
   begin
      P (O, Get_Kind (Node));
      P (O, " ");
      Print_Node (+Get_Orig_Name (Node));
      P (O, " = ");
      Print_Node (+Get_Image (Node));
   end Print_Clone_Substitution;

   -------------------
   -- Print_Comment --
   -------------------

   procedure Print_Comment (Node : W_Comment_Id) is
   begin
      P (O, "() (* ");
      P (O, Get_Comment (Node));
      PL (O, " *)");
   end Print_Comment;

   ------------------------
   -- Print_Conditional --
   ------------------------

   procedure Print_Conditional (Node : W_Conditional_Id) is
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
      Print_Node (+Condition);

      PL (O, ") then (");
      Relative_Indent (O, 1);
      Print_Node (+Then_Part);
      Relative_Indent (O, -1);
      P (O, ")");

      if not Is_Empty (+Elsif_Parts) then
         Print_List (+Elsif_Parts, Separator => " ");
      end if;

      if Has_Else then
         P (O, " else (");

         if not Has_Elsif then
            NL (O);
            Relative_Indent (O, 1);
         end if;

         Print_Node (+Else_Part);

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
   end Print_Conditional;

   ------------------------
   -- Print_Connection --
   ------------------------

   procedure Print_Connection (Node  : W_Connection_Id) is
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
      Print_Node (+Left);
      P (O, " ");
      P (O, Op);
      P (O, " ");
      Print_Node (+Right);
      P (O, " )");

      if not Is_Empty (+More_Right) then
         for E of Get_List (Why_Node_List (More_Right)) loop
            P (O, " ");
            P (O, Op);
            P (O, " ");
            Print_Node (+E);
            P (O, " )");
         end loop;
      end if;
   end Print_Connection;

   -------------------------------
   -- Print_Custom_Declaration --
   -------------------------------

   procedure Print_Custom_Declaration (Node  : W_Custom_Declaration_Id) is
      use GNAT.Regpat;

      function Get_Whole_File return String;
      --  Return whole contents of file associated with Node

      function Get_Regexp return String;
      --  Return the regexp that should be used to match the content of the
      --  file associated with Node. If the substitution associated with Node
      --  is : ((From => F1, To => T1), ..., (From => Fn, To => Tn)),
      --  return F1 & '|' & ... & '|' & Fn.

      procedure Apply_Subst (Text : String; Matches : Match_Array);
      --  Output the correct replacement for the match Matches in Text. If the
      --  substitution associated with Node is : ((From => F1, To => T1), ...,
      --  (From => Fn, To => Tn)), then try to match the substring of Text
      --  corresponding to Matches with F1, ... and then Fn. If a match is
      --  found with Fi then output Ti.
      --  Should be called on the result of a match with Get_Regexp.

      function Locate_File return String;
      --  Return name of file associated with Node

      -----------------
      -- Locate_File --
      -----------------

      function Locate_File return String is
         use Ada.Directories;

         Dir : String_Access := Locate_Exec_On_Path (Exec_Name => "gnatprove");

         function Get_Proof_Dir return String;
         --  Retrieve the name of the Proof_Dir project attribute from
         --  gnatwhy3's arguments.

         -------------------
         -- Get_Proof_Dir --
         -------------------

         function Get_Proof_Dir return String is
            Index : String_Lists.Cursor;
         begin
            Index := String_Lists.Find (Container => Gnat2Why_Args.Why3_Args,
                                        Item => "--proof-dir");

            if String_Lists.Has_Element (Index) then
               String_Lists.Next (Index);
               return String_Lists.Element (Index);
            end if;

            return "";
         end Get_Proof_Dir;
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
            Proof_Dir : constant String := Get_Proof_Dir;
            From_Proof_Dir : constant String :=
              Compose (Compose (Proof_Dir, "_theories"), File_Name);
         begin
            Free (Dir);

            if Is_Readable_File (From_Command) then
               return From_Command;
            elsif Proof_Dir /= ""
               and then Is_Readable_File (From_Proof_Dir)
            then
               return From_Proof_Dir;
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
         use Why_Node_Lists;

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
         use Why_Node_Lists;

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
                  Print_Node (+Get_To (Node));
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

      if Why_Node_Lists.Is_Empty (Get_List (+Get_Subst (Node))) then
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
   end Print_Custom_Declaration;

   ------------------
   -- Print_Deref --
   ------------------

   procedure Print_Deref (Node : W_Deref_Id) is
   begin
      P (O, "!");
      Print_Node (+Get_Right (Node));
   end Print_Deref;

   --------------------
   -- Print_Effects --
   --------------------

   procedure Print_Effects (Node  : W_Effects_Id)
   is
      Reads  : constant W_Identifier_List := Get_Reads (Node);
      Writes : constant W_Identifier_List := Get_Writes (Node);
      Raises : constant W_Identifier_List := Get_Raises (Node);
   begin
      if not Is_Empty (+Reads) then
         P (O, "reads {");
         Print_List (+Reads, ", ");
         PL (O, " }");
      end if;

      if not Is_Empty (+Writes) then
         P (O, "writes {");
         Print_List (+Writes, ", ");
         PL (O, " }");
      end if;

      if not Is_Empty (+Raises) then
         P (O, "raises { ");
         Print_List (+Raises, ", ");
         PL (O, " }");
      end if;
   end Print_Effects;

   ------------------
   -- Print_Elsif --
   ------------------

   procedure Print_Elsif (Node : W_Elsif_Id) is
      Condition : constant W_Expr_Id := Get_Condition (Node);
      Then_Part : constant W_Expr_Id := Get_Then_Part (Node);
   begin
      P (O, " else if (");
      Print_Node (+Condition);
      PL (O, ") then (");
      Relative_Indent (O, 1);
      Print_Node (+Then_Part);
      Relative_Indent (O, -1);
      P (O, ")");
   end Print_Elsif;

   ----------------------------------
   -- Print_Exception_Declaration --
   ----------------------------------

   procedure Print_Exception_Declaration (Node : W_Exception_Declaration_Id) is
      Arg : constant W_Type_OId := Get_Arg (Node);
   begin
      P (O, "exception ");
      Print_Node (+Get_Name (Node));

      if Arg /= Why_Empty then
         P (O, "of ");
         Print_Node (+Arg);
      end if;
      NL (O);
   end Print_Exception_Declaration;

   --------------------------------
   -- Print_Existential_Quantif --
   --------------------------------

   procedure Print_Existential_Quantif (Node : W_Existential_Quantif_Id) is
      Variables       : constant W_Identifier_List := Get_Variables (Node);
      Var_Type        : constant W_Type_Id := Get_Var_Type (Node);
      Pred            : constant W_Pred_Id := Get_Pred (Node);
      Exists_Sequence : constant Boolean :=
        Get_Kind (+Pred) = W_Existential_Quantif;
   begin
      P (O, "(exists ");
      Print_List (+Variables, " ");
      P (O, " ");
      P (O, Get_Labels (Node), As_String => True);

      P (O, " : ");
      Print_Node (+Var_Type);
      PL (O, ".");

      if not Exists_Sequence then
         Relative_Indent (O, 1);
      end if;

      Print_Node (+Pred);

      if not Exists_Sequence then
         Relative_Indent (O, -1);
      end if;
      P (O, ")");
   end Print_Existential_Quantif;

   --------------------------
   -- Print_Exn_Condition --
   --------------------------

   procedure Print_Exn_Condition (Node : W_Exn_Condition_Id)
   is
   begin
      P (O, "| ");
      Print_Node (+Get_Exn_Case (Node));
      P (O, " => ");
      Print_Node (+Get_Pred (Node));
   end Print_Exn_Condition;

   -----------------------------
   -- Print_Field_Association --
   -----------------------------

   procedure Print_Field_Association (Node : W_Field_Association_Id) is
   begin
      Print_Node (+Get_Field (Node));
      P (O, " = ");
      Print_Node (+Get_Value (Node));
   end Print_Field_Association;

   -----------------
   -- Print_File --
   -----------------

   procedure Print_File (Node : W_File_Id) is
   begin
      Print_List (+Get_Theories (Node), "", Newline => True);
   end Print_File;

   ---------------------------
   -- Print_Fixed_Constant --
   ---------------------------

   procedure Print_Fixed_Constant (Node : W_Fixed_Constant_Id) is
      Value : constant Uint := Get_Value (Node);
   begin
      if Value < Uint_0 then
         P (O, "( ");
         P (O, Value);
         P (O, " )");
      else
         P (O, Value);
      end if;
   end Print_Fixed_Constant;

   --------------------------
   -- Print_Function_Decl --
   --------------------------

   procedure Print_Function_Decl (Node : W_Function_Decl_Id) is
      Name        : constant W_Identifier_Id := Get_Name (Node);
      Return_Type : constant W_Type_Id := Get_Return_Type (Node);
      Binders     : constant W_Binder_OList := Get_Binders (Node);
      Def         : constant W_Expr_Id := Get_Def (Node);
   begin
      case Get_Domain (+Node) is
         when EW_Term =>
            P (O, "function ");

            Print_Node (+Name);

            P (O, " ");
            P (O, Get_Labels (Node), As_String => True);

            NL (O);
            Relative_Indent (O, 1);

            if not Is_Empty (+Binders) then
               P (O, " (");
               Print_List (+Binders, ") (");
               P (O, ") ");
            end if;
            P (O, " :");
            Print_Node (+Return_Type);

            if Def /= Why_Empty then
               PL (O, " =");
               Print_Node (+Def);
            end if;

            Relative_Indent (O, -1);
            NL (O);

         when EW_Prog =>
            if Def = Why_Empty then
               P (O, "val ");
            else
               P (O, "let ");
            end if;

            Print_Node (+Name);
            P (O, " ");
            P (O, Get_Labels (Node), As_String => True);
            Relative_Indent (O, 1);
            NL (O);
            declare
               Pre         : constant W_Pred_Id := Get_Pre (Node);
               Effects     : constant W_Effects_Id := Get_Effects (Node);
               Post        : constant W_Pred_Id := Get_Post (Node);
            begin
               if not Is_Empty (+Binders) then
                  P (O, " (");
                  Print_List (+Binders, ") (");
                  P (O, ") ");
               end if;

               if Def = Why_Empty then
                  P (O, " :");
                  Print_Node (+Return_Type);
               end if;
               NL (O);
               if Pre /= Why_Empty then
                  P (O, "requires { ");
                  Print_Node (+Pre);
                  P (O, " }");
                  NL (O);
               end if;
               if Post /= Why_Empty then
                  P (O, "ensures { ");
                  Print_Node (+Post);
                  P (O, " }");
                  NL (O);
               end if;
               if Effects /= Why_Empty then
                  Print_Node (+Effects);
                  NL (O);
               end if;
               if Def /= Why_Empty then
                  PL (O, " =");
                  Print_Node (+Def);
               end if;
               Relative_Indent (O, -1);
            end;

         when EW_Pred =>
            P (O, "predicate ");

            Print_Node (+Name);

            NL (O);
            Relative_Indent (O, 1);

            if not Is_Empty (+Binders) then
               P (O, " (");
               Print_List (+Binders, ") (");
               P (O, ") ");
            end if;

            if Def /= Why_Empty then
               PL (O, " =");
               Print_Node (+Def);
            end if;

            Relative_Indent (O, -1);
            NL (O);
      end case;
   end Print_Function_Decl;

   -----------------------------------
   -- Print_Global_Ref_Declaration --
   -----------------------------------

   procedure Print_Global_Ref_Declaration (Node : W_Global_Ref_Declaration_Id)
   is
   begin
      P (O, "val ");
      Print_Node (+Get_Name (Node));

      P (O, " ");
      P (O, Get_Labels (Node), As_String => True);

      P (O, " : ref ");
      Print_Node (+Get_Ref_Type (Node));
      NL (O);
   end Print_Global_Ref_Declaration;

   -----------------
   -- Print_Goal --
   -----------------

   procedure Print_Goal (Node : W_Goal_Id) is
   begin
      P (O, "goal ");
      P (O, Get_Name (Node));
      PL (O, " :");
      Relative_Indent (O, 1);
      Print_Node (+Get_Def (Node));
      Relative_Indent (O, -1);
      NL (O);
   end Print_Goal;

   --------------------
   -- Print_Handler --
   --------------------

   procedure Print_Handler (Node : W_Handler_Id) is
      Arg : constant W_Prog_OId := Get_Arg (Node);
   begin
      Print_Node (+Get_Name (Node));

      if Arg /= Why_Empty then
         P (O, " ");
         Print_Node (+Arg);
      end if;

      P (O, " -> ");
      Print_Node (+Get_Def (Node));
   end Print_Handler;

   -----------------------
   -- Print_Identifier --
   -----------------------

   procedure Print_Identifier (Node : W_Identifier_Id) is
      Module : constant W_Module_Id := Get_Module (Node);
   begin
      if Module /= Why_Empty
        and then Get_Name (Module) /= No_Name
      then
         Print_Module_Id (Module);
         P (O, ".");
      end if;
      P (O, Get_Symbol (Node));
   end Print_Identifier;

   --------------------------------
   -- Print_Include_Declaration --
   --------------------------------

   procedure Print_Include_Declaration (Node  : W_Include_Declaration_Id) is
   begin
      P (O, "use ");
      P (O, Get_Use_Kind (Node));
      P (O, " ");
      Print_Module_Id (Get_Module (Node), With_File => True);
      NL (O);
   end Print_Include_Declaration;

   -----------------------------
   -- Print_Integer_Constant --
   -----------------------------

   procedure Print_Integer_Constant (Node : W_Integer_Constant_Id) is
      Value : constant Uint := Get_Value (Node);
   begin
      if Value < Uint_0 then
         P (O, "( ");
         P (O, Value);
         P (O, " )");
      else
         P (O, Value);
      end if;
   end Print_Integer_Constant;

   ------------------
   -- Print_Label --
   ------------------

   procedure Print_Label (Node : W_Label_Id) is
      use Why_Node_Lists;

      Labels : constant Name_Id_Set := Get_Labels (Node);
   begin
      if not Labels.Is_Empty then
         P (O, "( ");
      end if;
      P (O, Labels, As_String => True);
      Print_Node (+Get_Def (Node));
      if not Labels.Is_Empty then
         P (O, " )");
      end if;
   end Print_Label;

   ----------------
   -- Print_List --
   ----------------

   procedure Print_List
     (List_Id   : Why_Node_List;
      Separator : String := ", ";
      Newline   : Boolean := False)
   is
      use Why_Node_Lists;

      Nodes    : constant List := Get_List (List_Id);
      Position : Cursor := First (Nodes);
   begin
      while Position /= No_Element loop
         declare
            Node : constant Why_Node_Id := Element (Position);
         begin
            Print_Node (Node);
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

   --------------------
   -- Print_Literal --
   --------------------

   procedure Print_Literal (Node : W_Literal_Id) is
   begin
      P (O, Get_Value (Node), Get_Domain (+Node));
   end Print_Literal;

   -----------------------
   -- Print_Loop_Annot --
   -----------------------

   procedure Print_Loop_Annot (Node : W_Loop_Annot_Id) is
      Invariant : constant W_Pred_OId := Get_Invariant (Node);
   begin
      if Invariant /= Why_Empty then
         P (O, "invariant ");
         PL (O, "{ ");
         Relative_Indent (O, 1);
         Print_Node (+Invariant);
         NL (O);
         Relative_Indent (O, -1);
         P (O, " }");
      end if;
   end Print_Loop_Annot;

   ---------------------
   -- Print_Module_Id --
   ---------------------

   procedure Print_Module_Id
     (Node      : W_Module_Id;
      With_File : Boolean := False)
   is
      File : constant Name_Id := Get_File (Node);
   begin
      if With_File
        and then File /= No_Name
      then
         P (O, """");
         P (O, File);
         P (O, """.");
      end if;
      P (O, Capitalize_First (Get_Name_String (Get_Name (Node))));
   end Print_Module_Id;

   ----------------
   -- Print_Name --
   ----------------

   procedure Print_Name (Node : W_Name_Id) is
      Module : constant W_Module_Id := Get_Module (Node);
   begin
      if Module /= Why_Empty
        and then Get_Name (Module) /= No_Name
      then
         Print_Module_Id (Module);
         P (O, ".");
      end if;
      P (O, Get_Symbol (Node));
   end Print_Name;

   ----------------
   -- Print_Node --
   ----------------

   procedure Print_Node (N : Why_Node_Id) is
   begin
      case Get_Kind (N) is
         when W_Unused_At_Start =>
            null;

         when W_Type =>
            Print_Type (+N);

         when W_Effects =>
            Print_Effects (+N);

         when W_Binder =>
            Print_Binder (+N);

         when W_Transparent_Type_Definition =>
            Print_Transparent_Type_Definition (+N);

         when W_Record_Definition =>
            Print_Record_Definition (+N);

         when W_Triggers =>
            Print_Triggers (+N);

         when W_Trigger =>
            Print_Trigger (+N);

         when W_Postcondition =>
            Print_Postcondition (+N);

         when W_Exn_Condition =>
            Print_Exn_Condition (+N);

         when W_Loop_Annot =>
            Print_Loop_Annot (+N);

         when W_Handler =>
            Print_Handler (+N);

         when W_Field_Association =>
            Print_Field_Association (+N);

         when W_Universal_Quantif =>
            Print_Universal_Quantif (+N);

         when W_Existential_Quantif =>
            Print_Existential_Quantif (+N);

         when W_Not =>
            Print_Not (+N);

         when W_Relation =>
            Print_Relation (+N);

         when W_Connection =>
            Print_Connection (+N);

         when W_Label =>
            Print_Label (+N);

         when W_Identifier =>
            Print_Identifier (+N);

         when W_Name =>
            Print_Name (+N);

         when W_Tagged =>
            Print_Tagged (+N);

         when W_Call =>
            Print_Call (+N);

         when W_Literal =>
            Print_Literal (+N);

         when W_Binding =>
            Print_Binding (+N);

         when W_Elsif =>
            Print_Elsif (+N);

         when W_Conditional =>
            Print_Conditional (+N);

         when W_Integer_Constant =>
            Print_Integer_Constant (+N);

         when W_Fixed_Constant =>
            Print_Fixed_Constant (+N);

         when W_Real_Constant =>
            Print_Real_Constant (+N);

         when W_Void =>
            Print_Void (+N);

         when W_Comment =>
            Print_Comment (+N);

         when W_Binary_Op =>
            Print_Binary_Op (+N);

         when W_Unary_Op =>
            Print_Unary_Op (+N);

         when W_Deref =>
            Print_Deref (+N);

         when W_Record_Access =>
            Print_Record_Access (+N);

         when W_Record_Update =>
            Print_Record_Update (+N);

         when W_Record_Aggregate =>
            Print_Record_Aggregate (+N);

         when W_Any_Expr =>
            Print_Any_Expr (+N);

         when W_Assignment =>
            Print_Assignment (+N);

         when W_Binding_Ref =>
            Print_Binding_Ref (+N);

         when W_While_Loop =>
            Print_While_Loop (+N);

         when W_Statement_Sequence =>
            Print_Statement_Sequence (+N);

         when W_Abstract_Expr =>
            Print_Abstract_Expr (+N);

         when W_Assert =>
            Print_Assert (+N);

         when W_Raise =>
            Print_Raise (+N);

         when W_Try_Block =>
            Print_Try_Block (+N);

         when W_Function_Decl =>
            Print_Function_Decl (+N);

         when W_Axiom =>
            Print_Axiom (+N);

         when W_Goal =>
            Print_Goal (+N);

         when W_Type_Decl =>
            Print_Type_Decl (+N);

         when W_Global_Ref_Declaration =>
            Print_Global_Ref_Declaration (+N);

         when W_Exception_Declaration =>
            Print_Exception_Declaration (+N);

         when W_Include_Declaration =>
            Print_Include_Declaration (+N);

         when W_Clone_Declaration =>
            Print_Clone_Declaration (+N);

         when W_Clone_Substitution =>
            Print_Clone_Substitution (+N);

         when W_Theory_Declaration =>
            Print_Theory_Declaration (+N);

         when W_Custom_Substitution =>
            pragma Assert (False);

         when W_Custom_Declaration =>
            Print_Custom_Declaration (+N);

         when W_Module =>
            Print_Module_Id (+N);

         when W_File =>
            Print_File (+N);
      end case;
   end Print_Node;

   ----------------
   -- Print_Not --
   ----------------

   procedure Print_Not (Node : W_Not_Id) is
      Pred : constant W_Expr_Id := +Not_Get_Right (+Node);
   begin
      P (O, "not ( ");
      Print_Node (+Pred);
      P (O, " )");
   end Print_Not;

   --------------------------
   -- Print_Postcondition --
   --------------------------

   procedure Print_Postcondition (Node : W_Postcondition_Id)
   is
      Handlers : constant W_Exn_Condition_OList := Get_Handlers (Node);
   begin
      Print_Node (+Get_Pred (Node));

      if not Is_Empty (+Handlers) then
         NL (O);
         Relative_Indent (O, 1);
         Print_List (+Handlers, "", Newline => True);
         Relative_Indent (O, -1);
      end if;
   end Print_Postcondition;

   ------------------
   -- Print_Raise --
   ------------------

   procedure Print_Raise (Node : W_Raise_Id) is
      Exn_Type : constant W_Type_OId := Get_Exn_Type (Node);
   begin
      P (O, "raise ");

      Print_Node (+Get_Name (Node));

      if Exn_Type /= Why_Empty then
         P (O, " : ");
         Print_Node (+Exn_Type);
      end if;
   end Print_Raise;

   --------------------------
   -- Print_Real_Constant --
   --------------------------

   procedure Print_Real_Constant (Node : W_Real_Constant_Id) is
   begin
      P (O, "(");
      P (O, Get_Value (Node));
      P (O, ")");
   end Print_Real_Constant;

   --------------------------
   -- Print_Record_Access --
   --------------------------

   procedure Print_Record_Access (Node : W_Record_Access_Id) is
   begin
      Print_Node (+Get_Name (Node));
      P (O, ".");
      Print_Node (+Get_Field (Node));
   end Print_Record_Access;

   -----------------------------
   -- Print_Record_Aggregate --
   -----------------------------

   procedure Print_Record_Aggregate (Node : W_Record_Aggregate_Id) is
   begin
      P (O, "{ ");
      Print_List (+Get_Associations (Node), "; ");
      P (O, " }");
   end Print_Record_Aggregate;

   ------------------------------
   -- Print_Record_Definition --
   ------------------------------

   procedure Print_Record_Definition (Node : W_Record_Definition_Id)
   is
   begin
      P (O, "{ ");
      Print_List (+Get_Fields (Node), "; ");
      P (O, " }");
   end Print_Record_Definition;

   --------------------------
   -- Print_Record_Update --
   --------------------------

   procedure Print_Record_Update (Node : W_Record_Update_Id) is
   begin
      P (O, "{ ( ");
      Print_Node (+Get_Name (Node));
      P (O, " ) with ");
      Print_List (+Get_Updates (Node), "; ");
      P (O, " }");
   end Print_Record_Update;

   ---------------------
   -- Print_Relation --
   ---------------------

   procedure Print_Relation (Node : W_Relation_Id) is
      Left   : constant W_Expr_Id := Get_Left (Node);
      Op     : constant EW_Relation := Get_Op (Node);
      Right  : constant W_Expr_Id := Get_Right (Node);
      Op2    : constant EW_Relation := Get_Op2 (Node);
      Right2 : constant W_Expr_OId := Get_Right2 (Node);
   begin
      P (O, "( ");
      Print_Node (+Left);
      P (O, " ");
      P (O, Op, Get_Op_Type (Node));
      P (O, " ");
      Print_Node (+Right);

      if Op2 /= EW_None then
         P (O, " ");
         P (O, Op2, Get_Op_Type (Node));
         P (O, " ");
         Print_Node (+Right2);
      end if;
      P (O, " )");
   end Print_Relation;

   ---------------------
   -- Sprint_Why_Node --
   ---------------------

   procedure Sprint_Why_Node (Node : Why_Node_Id; To : Output_Id := Stdout) is
   begin
      O := To;
      Print_Node (Node);
   end Sprint_Why_Node;

   -------------------------------
   -- Print_Statement_Sequence --
   -------------------------------

   procedure Print_Statement_Sequence (Node : W_Statement_Sequence_Id) is
   begin
      P (O, "( ");
      Print_List (+Get_Statements (Node), ";", Newline => True);
      P (O, " )");
   end Print_Statement_Sequence;

   -----------------------
   -- Print_Tagged --
   -----------------------

   procedure Print_Tagged (Node : W_Tagged_Id) is
      Tag : constant Name_Id := Get_Tag (Node);
   begin
      if Tag = No_Name then
         Print_Node (+Get_Def (Node));
      elsif Tag = Old_Tag then
         P (O, "(old ");
         Print_Node (+Get_Def (Node));
         P (O, " )");
      else
         P (O, "(at ");
         Print_Node (+Get_Def (Node));
         P (O, " '");
         P (O, Tag);
         P (O, " )");
      end if;
   end Print_Tagged;

   -------------------------------
   -- Print_Theory_Declaration --
   -------------------------------

   procedure Print_Theory_Declaration (Node : W_Theory_Declaration_Id) is
      Kind : constant EW_Theory_Type := Get_Kind (Node);
   begin
      P (O, "(* ");
      P (O, Get_Comment (Node));
      PL (O, " *)");
      P (O, Kind, False);
      P (O, " ");
      P (O, Get_Name (Node));
      NL (O);
      Relative_Indent (O, 1);
      Print_List (+Get_Includes (Node), "", Newline => False);
      NL (O);
      Print_List (+Get_Declarations (Node), "", Newline => True);
      Relative_Indent (O, -1);
      NL (O);
      PL (O, "end");
   end Print_Theory_Declaration;

   ---------------------------------------
   -- Print_Transparent_Type_Definition --
   ---------------------------------------

   procedure Print_Transparent_Type_Definition
     (N : W_Transparent_Type_Definition_Id) is
   begin
      Print_Node (+Get_Type_Definition (N));
   end Print_Transparent_Type_Definition;

   --------------------
   -- Print_Trigger --
   --------------------

   procedure Print_Trigger (Node : W_Trigger_Id)
   is
      Terms    : constant W_Expr_OList := Get_Terms (Node);
   begin
      Print_List (+Terms);
   end Print_Trigger;

   ---------------------
   -- Print_Triggers --
   ---------------------

   procedure Print_Triggers (Node : W_Triggers_Id)
   is
      Triggers : constant W_Trigger_List := Get_Triggers (Node);
   begin
      P (O, "[");
      Print_List (+Triggers, " | ");
      P (O, "]");
   end Print_Triggers;

   ----------------------
   -- Print_Try_Block --
   ----------------------

   procedure Print_Try_Block (Node : W_Try_Block_Id) is
   begin
      PL (O, "try");
      Relative_Indent (O, 1);
      Print_Node (+Get_Prog (Node));
      Relative_Indent (O, -1);
      NL (O);
      PL (O, "with");
      Relative_Indent (O, 1);
      Print_List (+Get_Handler (Node), ", ", Newline => True);
      Relative_Indent (O, -1);
      NL (O);
      P (O, "end");
   end Print_Try_Block;

   ----------------
   -- Print_Type --
   ----------------

   procedure Print_Type (Node : W_Type_Id)
   is
      Base_Type : constant EW_Type := Get_Base_Type (Node);
      Name      : constant W_Name_Id := Get_Name (Node);
   begin
      if Get_Is_Mutable (Node) then
         P (O, "ref ");
      end if;
      if Present (Name) then
         Print_Node (+Name);
      elsif Base_Type = EW_Abstract then
         declare
            N : constant Node_Id := Get_Ada_Node (+Node);
         begin
            pragma Assert (N /= 0);
            P (O, Capitalize_First (Full_Name (N)));
            P (O, ".");
            P (O, Short_Name (N));
         end;
      else
         P (O, Base_Type);
      end if;
   end Print_Type;

   ---------------------
   -- Print_Type_Decl --
   ---------------------

   procedure Print_Type_Decl (Node : W_Type_Decl_Id) is
      use Why_Node_Lists;

      Args       : constant List := Get_List (+Get_Args (Node));
      Nb_Args    : constant Count_Type := Length (Args);
      Position   : Cursor := First (Args);
      Name       : constant W_Name_Id := Get_Name (Node);
      Definition : constant W_Type_Definition_Id := Get_Definition (Node);
   begin
      P (O, "type ");

      Print_Node (+Name);

      P (O, " ");
      P (O, Get_Labels (Node));

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
            Print_Node (Param);
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
         Print_Node (+Definition);
         Relative_Indent (O, -1);
      end if;
      NL (O);
   end Print_Type_Decl;

   ---------------------
   -- Print_Unary_Op --
   ---------------------

   procedure Print_Unary_Op (Node : W_Unary_Op_Id) is
      Op : constant EW_Unary_Op := Get_Op (Node);
   begin
      P (O, "( ");
      P (O, Op, Get_Op_Type (Node));
      P (O, " ");
      Print_Node (+Get_Right (Node));
      P (O, " )");
   end Print_Unary_Op;

   ------------------------------
   -- Print_Universal_Quantif --
   ------------------------------

   procedure Print_Universal_Quantif (Node : W_Universal_Quantif_Id) is
      Variables       : constant W_Identifier_List := Get_Variables (Node);
      Var_Type        : constant W_Type_Id := Get_Var_Type (Node);
      Triggers        : constant W_Triggers_OId := Get_Triggers (Node);
      Pred            : constant W_Pred_Id := Get_Pred (Node);
      Forall_Sequence : constant Boolean :=
        Get_Kind (+Pred) = W_Universal_Quantif;
   begin
      P (O, "(forall ");
      Print_List (+Variables, " ");
      P (O, " ");
      P (O, " : ");
      Print_Node (+Var_Type);

      if Triggers /= Why_Empty then
         P (O, " ");
         Print_Node (+Triggers);
      end if;

      PL (O, ".");

      if not Forall_Sequence then
         Relative_Indent (O, 1);
      end if;

      Print_Node (+Pred);

      if not Forall_Sequence then
         Relative_Indent (O, -1);
      end if;
      P (O, ")");
   end Print_Universal_Quantif;

   -----------------
   -- Print_Void --
   -----------------

   procedure Print_Void (Node : W_Void_Id) is
      pragma Unreferenced (Node);
   begin
      P (O, "()");
   end Print_Void;

   -----------------------
   -- Print_While_Loop --
   -----------------------

   procedure Print_While_Loop (Node : W_While_Loop_Id) is
      Condition    : constant W_Prog_Id := Get_Condition (Node);
      Annotation   : constant W_Loop_Annot_OId := Get_Annotation (Node);
      Loop_Content : constant W_Prog_Id := Get_Loop_Content (Node);
   begin
      P (O, "while ");
      Print_Node (+Condition);
      PL (O, " do");
      Relative_Indent (O, 1);

      if Annotation /= Why_Empty then
         Print_Node (+Annotation);
         NL (O);
      end if;

      Print_Node (+Loop_Content);
      Relative_Indent (O, -1);
      NL (O);
      P (O, "done");
   end Print_While_Loop;

   ---------
   -- wpg --
   ---------

   procedure wpg (Node : Why_Node_Id) is
   begin
      Sprint_Why_Node (Node, Stdout);
      NL (Stdout);
   end wpg;

end Why.Atree.Sprint;
