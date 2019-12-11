------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                     W H Y - A T R E E - S P R I N T                      --
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

with Ada.Containers;        use Ada.Containers;
with Ada.Direct_IO;
with Ada.Directories;
with Ada.Strings.Unbounded;
with Errout;                use Errout;
with Eval_Fat;
with Common_Containers;     use Common_Containers;
with GNAT.Regpat;
with GNAT.OS_Lib;           use GNAT.OS_Lib;
with Gnat2Why_Args;
with Namet;                 use Namet;
with SPARK_Atree;           use SPARK_Atree;
with SPARK_Util;            use SPARK_Util;
with Stand;
with String_Utils;          use String_Utils;
with Uintp;                 use Uintp;
with Why.Atree.Accessors;   use Why.Atree.Accessors;
with Why.Atree.Modules;     use Why.Atree.Modules;
with Why.Conversions;       use Why.Conversions;
with Why.Ids;               use Why.Ids;
with Why.Images;            use Why.Images;

package body Why.Atree.Sprint is

   O : Output_Id := Stdout;

   -----------------------------------
   -- Locations for counterexamples --
   -----------------------------------

   --  Counterexamples use Why3 locations, contrary to VCs which are based
   --  on special GP_Sloc labels. Due to shortcomings in Why3, source locations
   --  should be repeated inside expressions (see Print_Assert or
   --  Print_Any_Expr). When a Loc_Label node is traversed, the location is
   --  stored here for this purpose.

   Curr_Sloc   : Source_Ptr := No_Location;
   --  The source code location of currently printed node

   Curr_Marker : Symbol := No_Symbol;
   --  The marker for the source code location of currently printed node

   procedure Print_Sloc_Tag;
   --  Print the location tag for currently printed node

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Print_Node (N : Why_Node_Id);
   --  printing function for any node, calls the other functions in this
   --  package as needed

   type Print_Callback is access procedure (N : Why_Node_Id);

   procedure Print_List
     (Nodes     : Why_Node_Lists.List;
      Callback  : Print_Callback := Print_Node'Access;
      Separator : String := ", ";
      Newline   : Boolean := False;
      Loc       : Boolean := False);

   procedure Print_List
     (List_Id   : Why_Node_List;
      Callback  : Print_Callback := Print_Node'Access;
      Separator : String := ", ";
      Newline   : Boolean := False;
      Loc       : Boolean := False);
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
   procedure Print_Binder (Node : W_Binder_Id);
   procedure Print_Binding (Node : W_Binding_Id);
   procedure Print_Binding_Ref (Node : W_Binding_Ref_Id);
   procedure Print_Call (Node : W_Call_Id);
   procedure Print_Clone_Declaration (Node : W_Clone_Declaration_Id);
   procedure Print_Clone_Substitution (Node : W_Clone_Substitution_Id);
   procedure Print_Comment (Node : W_Comment_Id);
   procedure Print_Conditional (Node : W_Conditional_Id);
   procedure Print_Connection (Node : W_Connection_Id);
   procedure Print_Connection_List
     (Op         : EW_Connector;
      More_Right : W_Expr_OList);
   procedure Print_Custom_Declaration (Node : W_Custom_Declaration_Id);
   procedure Print_Deref (Node : W_Deref_Id);
   procedure Print_Effects (Node : W_Effects_Id);
   procedure Print_Elsif (Node : W_Elsif_Id);
   procedure Print_Epsilon (Node : W_Epsilon_Id);
   procedure Print_Exception_Declaration (Node : W_Exception_Declaration_Id);
   procedure Print_Existential_Quantif (Node : W_Existential_Quantif_Id);
   procedure Print_Exn_Condition (Node : W_Exn_Condition_Id);
   procedure Print_Field_Association (Node : W_Field_Association_Id);
   procedure Print_Fixed_Constant (Node : W_Fixed_Constant_Id);
   procedure Print_Float_Constant (Node : W_Float_Constant_Id);
   procedure Print_Function_Decl (Node : W_Function_Decl_Id);
   procedure Print_Global_Ref_Declaration (Node : W_Global_Ref_Declaration_Id);
   procedure Print_Goal (Node : W_Goal_Id);
   procedure Print_Handler (Node : W_Handler_Id);
   procedure Print_Identifier (Node : W_Identifier_Id);
   procedure Print_Include_Declaration (Node : W_Include_Declaration_Id);
   procedure Print_Integer_Constant (Node : W_Integer_Constant_Id);
   procedure Print_Meta_Declaration (Node : W_Meta_Declaration_Id);
   procedure Print_Modular_Constant (Node : W_Modular_Constant_Id);
   procedure Print_Label (Node : W_Label_Id);
   procedure Print_Literal (Node : W_Literal_Id);
   procedure Print_Loc_Label (Node : W_Loc_Label_Id);
   procedure Print_Name (Node : W_Name_Id);
   procedure Print_Name_Force_Prefix (Node : W_Name_Id);
   procedure Print_Namespace_Declaration (Node : W_Namespace_Declaration_Id);
   procedure Print_Not (Node : W_Not_Id);
   procedure Print_Postcondition (Node : W_Postcondition_Id);
   procedure Print_Raise (Node : W_Raise_Id);
   procedure Print_Range_Constant (Node : W_Range_Constant_Id);
   procedure Print_Range_Type_Definition (Node : W_Range_Type_Definition_Id);
   procedure Print_Real_Constant (Node : W_Real_Constant_Id);
   procedure Print_Record_Access (Node : W_Record_Access_Id);
   procedure Print_Record_Aggregate (Node : W_Record_Aggregate_Id);
   procedure Print_Record_Binder (Node : W_Record_Binder_Id);
   procedure Print_Record_Definition (Node : W_Record_Definition_Id);
   procedure Print_Record_Update (Node : W_Record_Update_Id);
   procedure Print_Statement_Sequence
     (Node  : W_Statement_Sequence_Id;
      Paren : Boolean := True);
   procedure Print_Tagged (Node : W_Tagged_Id);
   procedure Print_Theory_Declaration (Node : W_Theory_Declaration_Id);
   procedure Print_Transparent_Type_Definition
      (N : W_Transparent_Type_Definition_Id);
   procedure Print_Trigger (Node : W_Trigger_Id);
   procedure Print_Triggers (Node : W_Triggers_Id);
   procedure Print_Try_Block (Node : W_Try_Block_Id);
   procedure Print_Type (Node : W_Type_Id);
   procedure Print_Type_Decl (Node : W_Type_Decl_Id);
   procedure Print_Universal_Quantif (Node   : W_Universal_Quantif_Id);
   procedure Print_While_Loop (Node : W_While_Loop_Id);

   procedure Print_Inner_Sequence (N : Why_Node_Id);
   --  callback for the printing of sequences, to avoid too many parens when
   --  nesting sequences

   -------------------------
   -- Print_Abstract_Expr --
   -------------------------

   procedure Print_Abstract_Expr (Node : W_Abstract_Expr_Id) is
      Post : constant W_Pred_Id := Get_Post (Node);
   begin
      P (O, "begin ");
      P (O, "ensures {");
      Print_Node (+Post);
      P (O, "} ");
      P (O, "let _ = ");
      Print_Node (+Get_Expr (Node));
      P (O, " in () end ");
   end Print_Abstract_Expr;

   --------------------
   -- Print_Any_Expr --
   --------------------

   procedure Print_Any_Expr (Node : W_Any_Expr_Id) is
      Res_Ty  : constant W_Type_Id := Get_Return_Type (Node);
      Effects : constant W_Effects_Id := Get_Effects (Node);
      Pre     : constant W_Pred_Id := Get_Pre (Node);
      Post    : constant W_Pred_Id := Get_Post (Node);
      Labels  : constant Symbol_Sets.Set := Get_Labels (Node);
   begin
      P (O, "(val _f : ");
      Print_Node (+Res_Ty);
      NL (O);
      if Pre /= Why_Empty then
         P (O, "requires {");

         --  Print locations labels for the VC for the precondition if any

         if not Labels.Is_Empty then
            P (O, "( ");
         end if;
         P (O, Labels, As_Labels => True);

         Print_Sloc_Tag;
         Print_Node (+Pre);

         if not Labels.Is_Empty then
            P (O, " )");
         end if;
         PL (O, "} ");
      end if;
      if Post /= Why_Empty then
         P (O, "ensures {");
         Print_Sloc_Tag;
         Print_Node (+Post);
         PL (O, "} ");
      end if;
      if Effects /= Why_Empty then
         Print_Node (+Effects);
         NL (O);
      end if;
      P (O, "in _f)");
   end Print_Any_Expr;

   ------------------
   -- Print_Assert --
   ------------------

   procedure Print_Assert (Node : W_Assert_Id) is
   begin
      P (O, Get_Assert_Kind (Node));
      P (O, " { ");
      Print_Sloc_Tag;
      Print_Node (+Get_Pred (Node));
      P (O, " }");
   end Print_Assert;

   ----------------------
   -- Print_Assignment --
   ----------------------

   procedure Print_Assignment (Node : W_Assignment_Id) is
      Labels : constant Symbol_Set := Get_Labels (Node);
   begin
      P (O, "(");
      if not Labels.Is_Empty then
         P (O, "(");
         P (O, Labels, As_Labels => True);
      end if;
      Print_Node (+Get_Name (Node));
      if not Labels.Is_Empty then
         P (O, ")");
      end if;
      P (O, ".");
      pragma Assert (Get_Typ (Node) /= Why_Empty);
      Print_Node (+Get_Typ (Node));
      P (O, "__content");
      P (O, " <- ( ");
      Print_Node (+Get_Value (Node));
      P (O, " ))");
   end Print_Assignment;

   -----------------
   -- Print_Axiom --
   -----------------

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

   ------------------
   -- Print_Binder --
   ------------------

   procedure Print_Binder (Node  : W_Binder_Id)
   is
   begin
      Print_Node (+Get_Name (Node));
      P (O, " : ");
      Print_Node (+Get_Arg_Type (Node));
   end Print_Binder;

   -------------------
   -- Print_Binding --
   -------------------

   procedure Print_Binding (Node : W_Binding_Id) is
      Name             : constant W_Identifier_Id := Get_Name (Node);
      Def              : constant W_Expr_Id := Get_Def (Node);
      Context          : constant W_Expr_Id := Get_Context (Node);
      Binding_Sequence : constant Boolean := Get_Kind (+Context) = W_Binding;
   begin
      P (O, "(let ");
      Print_Node (+Name);
      P (O, " ");
      P (O, Identifier_Get_Labels (+Name), As_Labels => True);
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

   -----------------------
   -- Print_Binding_Ref --
   -----------------------

   procedure Print_Binding_Ref (Node : W_Binding_Ref_Id) is
      Name             : constant W_Identifier_Id := Get_Name (Node);
      Context          : constant W_Prog_Id := Get_Context (Node);
      Binding_Sequence : constant Boolean :=
        Get_Kind (+Context) = W_Binding_Ref;
   begin
      P (O, "let ");
      Print_Node (+Name);
      P (O, " ");
      P (O, Identifier_Get_Labels (+Name), As_Labels => True);
      P (O, " = { ");
      pragma Assert (Get_Typ (Name) /= Why_Empty);
      Print_Node (+Get_Typ (Name));
      P (O, "__content = ");
      Print_Node (+Get_Def (Node));
      PL (O, " } in ");

      if not Binding_Sequence then
         Relative_Indent (O, 1);
      end if;

      Print_Node (+Context);

      if not Binding_Sequence then
         Relative_Indent (O, -1);
      end if;
   end Print_Binding_Ref;

   ----------------
   -- Print_Call --
   ----------------

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
      if Get_Infix (Get_Name (Name)) then
         declare
            use Why_Node_Lists;

            Nodes       : constant List := Get_List (+Args);

            Left, Right : Why_Node_Id;
            C           : constant Cursor := First (Nodes);
         begin
            pragma Assert (Nodes.Length = 2);
            Left := Element (C);
            Right := Element (Next (C));
            Print_Node (Left);
            P (O, " ");
            Print_Node (+Name);
            P (O, " ");
            Print_Node (Right);
         end;
      else
         case Get_Domain (+Node) is
            when EW_Term
               | EW_Pred
               | EW_Pterm
            =>
               Print_Node (+Name);
               P (O, " ");
               Print_List (+Args, Separator => " ");

            when EW_Prog =>
               Print_Node (+Name);

               if not Is_Empty (+Args) then
                  P (O, "(");
                  Print_List (+Args, Separator => ") (");
                  P (O, ")");
               end if;
         end case;

      end if;
      P (O, ")");
   end Print_Call;

   -----------------------------
   -- Print_Clone_Declaration --
   -----------------------------

   procedure Print_Clone_Declaration (Node : W_Clone_Declaration_Id) is
      As_Name    : constant Symbol := Get_As_Name (Node);
      Subst_List : constant W_Clone_Substitution_OList :=
        +Get_Substitutions (Node);
   begin
      P (O, "clone ");
      P (O, Get_Clone_Kind (Node));
      P (O, " ");
      Print_Module_Id (Get_Origin (Node), With_File => True);
      if As_Name /= No_Symbol then
         P (O, " as ");
         P (O, As_Name);
      end if;

      --  Keep axioms as axioms, do not attempt to prove them

      P (O, " with axiom .");

      if not Is_Empty (+Subst_List) then
         P (O, ",");
         NL (O);
         Print_List (+Subst_List, Separator => ", ", Newline => True);
      end if;
      NL (O);
   end Print_Clone_Declaration;

   ------------------------------
   -- Print_Clone_Substitution --
   ------------------------------

   procedure Print_Clone_Substitution (Node : W_Clone_Substitution_Id) is
   begin
      P (O, Get_Kind (Node));
      P (O, " ");
      Print_Node (+Get_Orig_Name (Node));
      P (O, " = ");
      Print_Name_Force_Prefix (Get_Image (Node));
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

   -----------------------
   -- Print_Conditional --
   -----------------------

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

   ----------------------
   -- Print_Connection --
   ----------------------

   procedure Print_Connection (Node  : W_Connection_Id) is
      Left       : constant W_Expr_Id := Get_Left (Node);
      Op         : constant EW_Connector := Get_Op (Node);
      Right      : constant W_Expr_Id := Get_Right (Node);
      More_Right : constant W_Expr_OList := Get_More_Right (Node);
   begin
      if not Is_Empty (+More_Right) then
         P (O, "( ");
      end if;

      P (O, "( ");
      Print_Node (+Left);
      P (O, " ");
      P (O, Op);
      P (O, " ");
      Print_Node (+Right);
      P (O, " )");

      if not Is_Empty (+More_Right) then
         P (O, Op);
         Print_Connection_List (Op, More_Right);
         P (O, " )");
      end if;
   end Print_Connection;

   procedure Print_Connection_List
     (Op         : EW_Connector;
      More_Right : W_Expr_OList)
   is
      procedure Print_Connection_List
        (Node_List : Why_Node_Lists.List;
         From      : in out Why_Node_Lists.Cursor;
         Length    : Count_Type)
      with Pre => Length >= 1
        and then Why_Node_Lists.Has_Element (From);
      --  Output a well balanced tree of binary operations to minimize the
      --  depth of the expression.

      procedure Print_Connection_List
        (Node_List : Why_Node_Lists.List;
         From      : in out Why_Node_Lists.Cursor;
         Length    : Count_Type)
      is
         use Why_Node_Lists;
      begin
         if Length = 1 then
            Print_Node (+Element (From));
            Next (From);
         else
            P (O, "( ");
            Print_Connection_List (Node_List, From, (Length + 1) / 2);
            P (O, Op);
            Print_Connection_List (Node_List, From, Length / 2);
            P (O, " )");
         end if;
      end Print_Connection_List;

      Node_List : Why_Node_Lists.List renames
        Get_List (Why_Node_List (More_Right));
      From      : Why_Node_Lists.Cursor := Node_List.First;
   begin
      if not Node_List.Is_Empty then
         Print_Connection_List (Node_List, From, Node_List.Length);
      end if;
      pragma Assert (not Why_Node_Lists.Has_Element (From));
   end Print_Connection_List;

   ------------------------------
   -- Print_Custom_Declaration --
   ------------------------------

   procedure Print_Custom_Declaration (Node : W_Custom_Declaration_Id) is
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
            L : constant String_Lists.List := Gnat2Why_Args.Why3_Args;
         begin
            Index := String_Lists.Find (Container => L,
                                        Item => "--proof-dir");

            if String_Lists.Has_Element (Index) then
               String_Lists.Next (Index);
               return String_Lists.Element (Index);
            end if;

            return "";
         end Get_Proof_Dir;

      --  Start of processing for Locate_File

      begin
         if Dir = null then
            Error_Msg_N
              ("cannot locate associated theory file", Get_Ada_Node (+Node));
            return "";
         end if;

         declare
            File_Name : constant String := Img (Get_File_Name (Node));

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
                 ("cannot read theory file " & File_Name,
                  Get_Ada_Node (+Node));
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
            File_String_IO.Read (File, Item => Contents);
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
               Append (Result, Img (Get_From (Node)));
            end;

            Position := Next (Position);

            if Position /= No_Element then
               Append (Result, "|");
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
               Match (Compile (Img (Get_From (Node))), Text,
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

   -----------------
   -- Print_Deref --
   -----------------

   procedure Print_Deref (Node : W_Deref_Id) is
   begin
      pragma Assert (Get_Typ (Node) /= Why_Empty);
      Print_Node (+Get_Right (Node));
      P (O, ".");
      Print_Node (+Get_Typ (Node));
      P (O, "__content");
   end Print_Deref;

   -------------------
   -- Print_Effects --
   -------------------

   procedure Print_Effects (Node  : W_Effects_Id)
   is
      Reads  : constant W_Identifier_List := Get_Reads (Node);
      Writes : constant W_Identifier_List := Get_Writes (Node);
      Raises : constant W_Identifier_List := Get_Raises (Node);
   begin
      if not Is_Empty (+Reads) then
         P (O, "reads {");
         Print_List (+Reads, Separator => ", ");
         PL (O, "}");
      end if;

      if not Is_Empty (+Writes) then
         P (O, "writes {");
         Print_List (+Writes, Separator => ", ");
         PL (O, "}");
      end if;

      if not Is_Empty (+Raises) then
         P (O, "raises { ");
         Print_List (+Raises, Separator => ", ");
         PL (O, "}");
      end if;
   end Print_Effects;

   -----------------
   -- Print_Elsif --
   -----------------

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

   -------------------
   -- Print_Epsilon --
   -------------------

   procedure Print_Epsilon (Node : W_Epsilon_Id) is
      Name : constant W_Identifier_Id := Get_Name (Node);
      Typ  : constant W_Type_Id := Get_Typ (Node);
      Pred : constant W_Pred_Id := Get_Pred (Node);
   begin
      P (O, "(epsilon ");
      Print_Node (+Name);
      P (O, " : ");
      Print_Node (+Typ);
      PL (O, ".");

      Relative_Indent (O, 1);
      Print_Node (+Pred);
      Relative_Indent (O, -1);

      P (O, ")");
   end Print_Epsilon;

   ---------------------------------
   -- Print_Exception_Declaration --
   ---------------------------------

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

   -------------------------------
   -- Print_Existential_Quantif --
   -------------------------------

   procedure Print_Existential_Quantif (Node : W_Existential_Quantif_Id) is
      Variables       : constant W_Identifier_List := Get_Variables (Node);
      Var_Type        : constant W_Type_Id := Get_Var_Type (Node);
      Pred            : constant W_Pred_Id := Get_Pred (Node);
      Exists_Sequence : constant Boolean :=
        Get_Kind (+Pred) = W_Existential_Quantif;
   begin
      P (O, "(exists ");
      Print_List (+Variables, Separator => " ");
      P (O, " ");
      P (O, Get_Labels (Node), As_Labels => True);

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

   -------------------------
   -- Print_Exn_Condition --
   -------------------------

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

   --------------------------
   -- Print_Fixed_Constant --
   --------------------------

   procedure Print_Fixed_Constant (Node : W_Fixed_Constant_Id) is
      Value : constant Uint := Get_Value (Node);
   begin
      P (O, "( ");
      if Value < Uint_0 then
         P (O, "( ");
         P (O, Value);
         P (O, " )");
      else
         P (O, Value);
      end if;

      --  Print the type of integer constants to help Why3 with type inference

      P (O, " : int )");
   end Print_Fixed_Constant;

   --------------------------
   -- Print_Float_Constant --
   --------------------------

   procedure Print_Float_Constant (Node : W_Float_Constant_Id) is

      procedure Print_Cast (V : Ureal; Ty : String);
      --  Print the cast of the value V into the type printed as Ty

      ----------------
      -- Print_Cast --
      ----------------

      procedure Print_Cast (V : Ureal; Ty : String) is
      begin
         P (O, "(");
         P (O, V);
         P (O, ":" & Ty & ")");
      end Print_Cast;

      Value : Ureal := Get_Value (Node);
      Base : constant Int := Rbase (Value);

      Typ : constant W_Type_Id := Get_Typ (Node);
      Prefix : constant String :=
        (if Typ = EW_Float_32_Type then
            "Float32."
         elsif Typ = EW_Float_64_Type then
            "Float64."
         else
            raise Program_Error);

   begin

      --  in case the format of value would get it printed as a fraction we
      --  call Machine to change its base : Why3 is not happy with a fraction
      --  for a float litteral.
      if Base = 0
        or else not (Base = 10
                     or else Denominator (Value) <= Uint_0
                     or else Can_Be_Printed_In_Decimal_Notation (Base))
      then
         Value := Eval_Fat.Machine (RT    =>
                                      (if Get_Typ (Node) = EW_Float_32_Type
                                       then Stand.Standard_Float
                                       else Stand.Standard_Long_Float),
                                    X     => Value,
                                    Mode  => Eval_Fat.Round_Even,
                                    Enode => Get_Ada_Node (+Node));
      end if;

      if UR_Is_Negative (Value) then
         P (O, "(" & Prefix & "neg ");
         Print_Cast (UR_Negate (Value), Prefix & "t");
         P (O, ")");
      else
         Print_Cast (Value, Prefix & "t");
      end if;
   end Print_Float_Constant;

   -------------------------
   -- Print_Function_Decl --
   -------------------------

   procedure Print_Function_Decl (Node : W_Function_Decl_Id) is
      Name        : constant W_Identifier_Id := Get_Name (Node);
      Return_Type : constant W_Type_Id := Get_Return_Type (Node);
      Binders     : constant W_Binder_OList := Get_Binders (Node);
      Def         : constant W_Expr_Id := Get_Def (Node);

      procedure Print_Header (Fun_Kind : String);
      --  Print header of the declaration of Node

      ------------------
      -- Print_Header --
      ------------------

      procedure Print_Header (Fun_Kind : String) is
      begin
         P (O, Fun_Kind & " ");

         Print_Node (+Name);

         P (O, " ");

         P (O, Get_Location (Node));
         P (O, Get_Labels (Node), As_Labels => True);

         NL (O);
         Relative_Indent (O, 1);

         if not Is_Empty (+Binders) then
            P (O, " (");
            Print_List (+Binders, Separator => ") (");
            P (O, ")");
         end if;

         if Get_Domain (+Node) /= EW_Pred
           and then Return_Type /= Why_Empty
         then
            P (O, " : ");
            Print_Node (+Return_Type);
         end if;
      end Print_Header;

   begin
      case Get_Domain (+Node) is
         when EW_Term  =>
            Print_Header ("function");

            if Def /= Why_Empty then
               PL (O, " =");
               Print_Node (+Def);
            end if;

            Relative_Indent (O, -1);
            NL (O);

         when EW_Pterm =>

            --  We need to declare a function which can be used both in the
            --  logic and in the program domain. We have several cases:
            --    * If the function has no parameter, declare a val constant
            --      with its definition (if any) as a post. Do not use let
            --      constants as the definition is a logic term.
            --    * If the function has parameters and no definition, generate
            --      a val function.
            --    * If the function has parameters and a definition, generate
            --      both a logic function with a definition, and a val with
            --      a post stating that it is equal to the logic function. Do
            --      not generate a let function as the definition is a logic
            --      term and do not generate a val function with a post as then
            --      the definition would be inlined at call site.

            if Is_Empty (+Binders) then
               Print_Header ("val constant");
               NL (O);

               if Def /= Why_Empty then
                  P (O, "ensures { result = ");
                  Print_Sloc_Tag;
                  Print_Node (+Def);
                  P (O, " }");
               end if;
            elsif Def = Why_Empty then
               Print_Header ("val function");
            else
               Print_Header ("function");
               PL (O, " =");
               Print_Node (+Def);
               Relative_Indent (O, -1);
               NL (O);

               Print_Header ("val");
               NL (O);
               P (O, "ensures { result = ");
               Print_Node (+Name);
               P (O, " (");
               Print_List (+Binders, Separator => ") (");
               P (O, ")");
               P (O, " }");
            end if;

            Relative_Indent (O, -1);
            NL (O);

         when EW_Prog =>

            --  Change to current sloc

            Curr_Sloc := Get_Location (Node);
            Curr_Marker := No_Symbol;

            if Def = Why_Empty then
               Print_Header ("val");
            else
               Print_Header ("let");
            end if;

            NL (O);
            declare
               Pre     : constant W_Pred_Id := Get_Pre (Node);
               Effects : constant W_Effects_Id := Get_Effects (Node);
               Post    : constant W_Pred_Id := Get_Post (Node);
            begin
               if Pre /= Why_Empty then
                  P (O, "requires { ");
                  Print_Sloc_Tag;
                  Print_Node (+Pre);
                  P (O, " }");
                  NL (O);
               end if;
               if Post /= Why_Empty then
                  P (O, "ensures { ");
                  Print_Sloc_Tag;
                  Print_Node (+Post);
                  P (O, " }");
                  NL (O);
               end if;
               if Effects /= Why_Empty then
                  Print_Node (+Effects);
               end if;
               if Def /= Why_Empty then
                  PL (O, " = [@vc:divergent]");
                  Print_Node (+Def);
               end if;
               Relative_Indent (O, -1);
            end;

            Curr_Sloc := No_Location;
            Curr_Marker := No_Symbol;

         when EW_Pred =>

            if Def = Why_Empty then
               Print_Header ("val predicate");
            else
               Print_Header ("predicate");

               PL (O, " =");

               --  Predicate can actually be substituted somewhere without its
               --  location. So, locations should also be printed here.

               P (O, Get_Location (Node));
               Print_Node (+Def);

               Relative_Indent (O, -1);
               NL (O);

               pragma Assert (not Is_Empty (+Binders));

               --  Also print a program declaration for the predicate

               Print_Header ("val");
               P (O, " : bool");
               NL (O);
               P (O, "ensures { result <-> ");
               Print_Node (+Name);
               P (O, " (");
               Print_List (+Binders, Separator => ") (");
               P (O, ")");
               P (O, " }");
            end if;

            Relative_Indent (O, -1);
            NL (O);
      end case;
   end Print_Function_Decl;

   ----------------------------------
   -- Print_Global_Ref_Declaration --
   ----------------------------------

   procedure Print_Global_Ref_Declaration (Node : W_Global_Ref_Declaration_Id)
   is
   begin
      P (O, "val ");
      Print_Node (+Get_Name (Node));

      P (O, " ");

      P (O, Get_Location (Node));

      P (O, Get_Labels (Node), As_Labels => True);

      P (O, " : ");
      Print_Node (+Get_Ref_Type (Node));
      P (O, "__ref ");
      NL (O);
   end Print_Global_Ref_Declaration;

   ----------------
   -- Print_Goal --
   ----------------

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

   -------------------
   -- Print_Handler --
   -------------------

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

   ----------------------
   -- Print_Identifier --
   ----------------------

   procedure Print_Identifier (Node : W_Identifier_Id) is
   begin
      Print_Name (Get_Name (Node));
   end Print_Identifier;

   -------------------------------
   -- Print_Include_Declaration --
   -------------------------------

   procedure Print_Include_Declaration (Node  : W_Include_Declaration_Id) is
      Kind : constant EW_Clone_Type := Get_Use_Kind (Node);
   begin
      P (O, "use ");
      P (O, Kind);
      P (O, " ");
      Print_Module_Id (Get_Module (Node), With_File => True);

      --  Import is the default in Why. If we want to keep the namespace, we
      --  have to reintroduce it.

      if Kind = EW_Clone_Default then
         P (O, " as ");
         Print_Module_Id (Get_Module (Node), With_File => False);
      end if;

      NL (O);
   end Print_Include_Declaration;

   --------------------------
   -- Print_Inner_Sequence --
   --------------------------

   procedure Print_Inner_Sequence (N : Why_Node_Id) is
   begin
      if Get_Kind (N) = W_Statement_Sequence then
         Print_Statement_Sequence (+N, Paren => False);
      else
         Print_Node (N);
      end if;
   end Print_Inner_Sequence;

   ----------------------------
   -- Print_Integer_Constant --
   ----------------------------

   procedure Print_Integer_Constant (Node : W_Integer_Constant_Id) is
      Value : constant Uint := Get_Value (Node);
   begin
      P (O, "(");
      if Value < Uint_0 then
         P (O, "( ");
         P (O, Value);
         P (O, ")");
      else
         P (O, Value);
      end if;

      --  Print the type of integer constants to help Why3 with type inference

      P (O, " : int)");
   end Print_Integer_Constant;

   ----------------------------
   -- Print_Meta_Declaration --
   ----------------------------

   procedure Print_Meta_Declaration (Node : W_Meta_Declaration_Id) is
      Name      : constant Symbol := Get_Name (Node);
      Parameter : constant Symbol := Get_Parameter (Node);
   begin
      P (O, "meta """);
      P (O, Name);
      P (O, """ ");
      P (O, Parameter);
      NL (O);

   end Print_Meta_Declaration;

   ----------------------------
   -- Print_Modular_Constant --
   ----------------------------

   procedure Print_Modular_Constant (Node : W_Modular_Constant_Id) is
      Value : constant Uint := Get_Value (Node);
      Typ : constant W_Type_Id := Get_Typ (Node);
   begin
      P (O, "( ");
      P (O, Value);
      P (O, " : ");
      if Typ = EW_BitVector_8_Type then
         P (O, "BV8.t");
      elsif Typ = EW_BitVector_16_Type then
         P (O, "BV16.t");
      elsif Typ = EW_BitVector_32_Type then
         P (O, "BV32.t");
      elsif Typ = EW_BitVector_64_Type then
         P (O, "BV64.t");
      else
         raise Unexpected_Node;
      end if;
      P (O, " )");
   end Print_Modular_Constant;

   -----------------
   -- Print_Label --
   -----------------

   procedure Print_Label (Node : W_Label_Id) is
      Labels : constant Symbol_Set := Get_Labels (Node);
   begin
      if not Labels.Is_Empty then
         P (O, "( ");
      end if;

      P (O, Labels, As_Labels => True);
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
      Callback  : Print_Callback := Print_Node'Access;
      Separator : String := ", ";
      Newline   : Boolean := False;
      Loc       : Boolean := False)
   is
      Nodes : constant Why_Node_Lists.List := Get_List (List_Id);
   begin
      Print_List (Nodes, Callback, Separator, Newline, Loc);
   end Print_List;

   procedure Print_List
     (Nodes     : Why_Node_Lists.List;
      Callback  : Print_Callback := Print_Node'Access;
      Separator : String := ", ";
      Newline   : Boolean := False;
      Loc       : Boolean := False)
   is
      use Why_Node_Lists;

      Position : Cursor := First (Nodes);
   begin
      while Position /= No_Element loop
         declare
            Node : constant Why_Node_Id := Element (Position);
         begin
            Callback (Node);
            if Loc then
               P (O, " ");
               Print_Sloc_Tag;
            end if;
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

   -------------------
   -- Print_Literal --
   -------------------

   procedure Print_Literal (Node : W_Literal_Id) is
   begin
      P (O, Get_Value (Node), Get_Domain (+Node));
   end Print_Literal;

   ---------------------
   -- Print_Loc_Label --
   ---------------------

   procedure Print_Loc_Label (Node : W_Loc_Label_Id) is
   begin
      Curr_Sloc := Get_Sloc (Node);
      Curr_Marker := Get_Marker (Node);
      P (O, "(");
      Print_Sloc_Tag;
      Print_Node (+Get_Def (Node));
      P (O, ")");
      Curr_Sloc := No_Location;
      Curr_Marker := No_Symbol;
   end Print_Loc_Label;

   ------------------------
   -- Print_Modules_List --
   ------------------------

   procedure Print_Modules_List
     (L : Why_Node_Lists.List; To : Output_Id) is
   begin
      O := To;
      Print_List (L, Separator => "", Newline => True);
   end Print_Modules_List;

   ---------------------
   -- Print_Module_Id --
   ---------------------

   procedure Print_Module_Id
     (Node      : W_Module_Id;
      With_File : Boolean := False)
   is
   begin
      if With_File then
         declare
            File : constant Symbol := Get_File (Node);
         begin
            if File /= No_Symbol then
               P (O, """");
               P (O, File);
               P (O, """.");
            end if;
         end;
      end if;

      P (O, Get_Name (Node));
   end Print_Module_Id;

   ----------------
   -- Print_Name --
   ----------------

   procedure Print_Name (Node : W_Name_Id) is
   begin
      if not Get_Infix (Node) then
         declare
            Module    : constant W_Module_Id := Get_Module (Node);
            Namespace : constant Symbol := Get_Namespace (Node);
         begin
            if Module /= Why_Empty
              and then Get_Name (Module) /= No_Symbol
            then
               Print_Module_Id (Module);
               P (O, ".");
            end if;

            if Namespace /= No_Symbol then
               P (O, Namespace);
               P (O, ".");
            end if;
         end;
      end if;

      P (O, Get_Symb (Node));
   end Print_Name;

   -----------------------------
   -- Print_Name_Force_Prefix --
   -----------------------------

   procedure Print_Name_Force_Prefix (Node : W_Name_Id) is
      Module    : constant W_Module_Id := Get_Module (Node);
      Namespace : constant Symbol := Get_Namespace (Node);
   begin
      if Module /= Why_Empty
        and then Get_Name (Module) /= No_Symbol
      then
         Print_Module_Id (Module);
         P (O, ".");
      end if;

      if Namespace /= No_Symbol
      then
         P (O, Namespace);
         P (O, ".");
      end if;

      if Get_Infix (Node)
      then
         P (O, "(");
         P (O, Get_Symb (Node));
         P (O, ")");
      else
         P (O, Get_Symb (Node));
      end if;
   end Print_Name_Force_Prefix;

   ---------------------------------
   -- Print_Namespace_Declaration --
   ---------------------------------

   procedure Print_Namespace_Declaration (Node : W_Namespace_Declaration_Id) is
   begin
      P (O, "scope ");
      P (O, Get_Name (Node));
      NL (O);
      Relative_Indent (O, 1);
      Print_List (+Get_Declarations (Node), Separator => "", Newline => True);
      Relative_Indent (O, -1);
      NL (O);
      PL (O, "end");
   end Print_Namespace_Declaration;

   ----------------
   -- Print_Node --
   ----------------

   procedure Print_Node (N : Why_Node_Id) is
      N_Kind : constant Why_Node_Kind := Get_Kind (N);
   begin
      case N_Kind is
         when W_Raise
            | W_While_Loop
            | W_Abstract_Expr
            | W_Any_Expr
            | W_Assert
            | W_Assignment
            | W_Binding_Ref
            | W_Try_Block
         =>
            --  Nodes where the location tag has to be printed and when it can
            --  be printed before the nodes.
            --  Location tags are printed in order to display correct locations
            --  in counterexamples.

            Print_Sloc_Tag;
         when others => null;
      end case;

      case N_Kind is
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

         when W_Record_Binder =>
            Print_Record_Binder (+N);

         when W_Record_Definition =>
            Print_Record_Definition (+N);

         when W_Range_Type_Definition =>
            Print_Range_Type_Definition (+N);

         when W_Triggers =>
            Print_Triggers (+N);

         when W_Trigger =>
            Print_Trigger (+N);

         when W_Postcondition =>
            Print_Postcondition (+N);

         when W_Exn_Condition =>
            Print_Exn_Condition (+N);

         when W_Handler =>
            Print_Handler (+N);

         when W_Field_Association =>
            Print_Field_Association (+N);

         when W_Universal_Quantif =>
            Print_Universal_Quantif (+N);

         when W_Existential_Quantif =>
            Print_Existential_Quantif (+N);

         when W_Epsilon =>
            Print_Epsilon (+N);

         when W_Not =>
            Print_Not (+N);

         when W_Connection =>
            Print_Connection (+N);

         when W_Label =>
            Print_Label (+N);

         when W_Loc_Label =>
            Print_Loc_Label (+N);

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

         when W_Range_Constant =>
            Print_Range_Constant (+N);

         when W_Modular_Constant =>
            Print_Modular_Constant (+N);

         when W_Fixed_Constant =>
            Print_Fixed_Constant (+N);

         when W_Real_Constant =>
            Print_Real_Constant (+N);

         when W_Float_Constant =>
            Print_Float_Constant (+N);

         when W_Comment =>
            Print_Comment (+N);

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

         when W_Namespace_Declaration =>
            Print_Namespace_Declaration (+N);

         when W_Exception_Declaration =>
            Print_Exception_Declaration (+N);

         when W_Include_Declaration =>
            Print_Include_Declaration (+N);

         when W_Clone_Declaration =>
            Print_Clone_Declaration (+N);

         when W_Clone_Substitution =>
            Print_Clone_Substitution (+N);

         when W_Meta_Declaration =>
            Print_Meta_Declaration (+N);

         when W_Theory_Declaration =>
            Print_Theory_Declaration (+N);

         when W_Custom_Substitution =>
            pragma Assert (False);

         when W_Custom_Declaration =>
            Print_Custom_Declaration (+N);

         when W_Module =>
            Print_Module_Id (+N);
      end case;
   end Print_Node;

   ---------------
   -- Print_Not --
   ---------------

   procedure Print_Not (Node : W_Not_Id) is
      Pred : constant W_Expr_Id := +Not_Get_Right (+Node);
   begin
      P (O, "not ( ");
      Print_Node (+Pred);
      P (O, " )");
   end Print_Not;

   -------------------------
   -- Print_Postcondition --
   -------------------------

   procedure Print_Postcondition (Node : W_Postcondition_Id)
   is
      Handlers : constant W_Exn_Condition_OList := Get_Handlers (Node);
   begin
      Print_Node (+Get_Pred (Node));

      if not Is_Empty (+Handlers) then
         NL (O);
         Relative_Indent (O, 1);
         Print_List (+Handlers, Separator => "", Newline => True);
         Relative_Indent (O, -1);
      end if;
   end Print_Postcondition;

   -----------------
   -- Print_Raise --
   -----------------

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
   -- Print_Range_Constant --
   --------------------------

   procedure Print_Range_Constant (Node : W_Range_Constant_Id) is
      Typ   : constant W_Type_Id := Get_Typ (Node);
      Value : constant Uint := Get_Value (Node);
   begin
      P (O, "( ");
      P (O, Value);
      P (O, " : ");
      Print_Node (+Typ);
      P (O, " )");
   end Print_Range_Constant;

   ---------------------------------
   -- Print_Range_Type_Definition --
   ---------------------------------

   procedure Print_Range_Type_Definition (Node : W_Range_Type_Definition_Id) is
      First : constant Uint := Get_First (Node);
      Last  : constant Uint := Get_Last (Node);
   begin
      P (O, "< range ");
      P (O, First);
      P (O, " ");
      P (O, Last);
      P (O, " >");
   end Print_Range_Type_Definition;

   -------------------------
   -- Print_Real_Constant --
   -------------------------

   procedure Print_Real_Constant (Node : W_Real_Constant_Id) is
   begin
      P (O, "(");
      P (O, Get_Value (Node));
      P (O, ")");
   end Print_Real_Constant;

   -------------------------
   -- Print_Record_Access --
   -------------------------

   procedure Print_Record_Access (Node : W_Record_Access_Id) is
   begin
      Print_Node (+Get_Name (Node));
      P (O, ".");
      Print_Node (+Get_Field (Node));
   end Print_Record_Access;

   ----------------------------
   -- Print_Record_Aggregate --
   ----------------------------

   procedure Print_Record_Aggregate (Node : W_Record_Aggregate_Id) is
   begin
      P (O, "{ ");
      Print_List (+Get_Associations (Node), Separator => "; ");
      P (O, " }");
   end Print_Record_Aggregate;

   -------------------------
   -- Print_Record_Binder --
   -------------------------

   procedure Print_Record_Binder (Node : W_Record_Binder_Id)
   is
   begin
      if Get_Is_Mutable (Node) then
         P (O, "mutable ");
      end if;
      Print_Node (+Get_Name (Node));
      P (O, " ");
      P (O, Get_Labels (Node), As_Labels => True);
      P (O, ": ");
      Print_Node (+Get_Arg_Type (Node));
   end Print_Record_Binder;

   -----------------------------
   -- Print_Record_Definition --
   -----------------------------

   procedure Print_Record_Definition (Node : W_Record_Definition_Id)
   is
   begin
      P (O, "{ ");
      Print_List (+Get_Fields (Node), Separator => "; ");
      P (O, " }");
   end Print_Record_Definition;

   -------------------------
   -- Print_Record_Update --
   -------------------------

   procedure Print_Record_Update (Node : W_Record_Update_Id) is
   begin
      P (O, "{ ( ");
      Print_Node (+Get_Name (Node));
      P (O, " ) with ");
      Print_List (+Get_Updates (Node), Separator => "; ");
      P (O, " }");
   end Print_Record_Update;

   --------------------
   -- Print_Sloc_Tag --
   --------------------

   procedure Print_Sloc_Tag is
   begin
      P (O, Curr_Sloc, Curr_Marker);
      P (O, " ");
   end Print_Sloc_Tag;

   ---------------------
   -- Sprint_Why_Node --
   ---------------------

   procedure Sprint_Why_Node (Node : Why_Node_Id; To : Output_Id := Stdout) is
   begin
      O := To;
      Print_Node (Node);
   end Sprint_Why_Node;

   procedure Print_Section
     (WF : Why_Section; To : Output_Id := Stdout) is
   begin
      O := To;
      Print_List (WF.Theories, Separator => "", Newline => True);
   end Print_Section;

   ------------------------------
   -- Print_Statement_Sequence --
   ------------------------------

   procedure Print_Statement_Sequence
     (Node  : W_Statement_Sequence_Id;
      Paren : Boolean := True) is
   begin
      if Paren then
         P (O, "( ");
      end if;
      Print_List (+Get_Statements (Node),
                  Callback  => Print_Inner_Sequence'Access,
                  Separator => ";",
                  Newline   => True);
      if Paren then
         P (O, " )");
      end if;
   end Print_Statement_Sequence;

   ------------------
   -- Print_Tagged --
   ------------------

   procedure Print_Tagged (Node : W_Tagged_Id) is
      Tag : constant Symbol := Get_Tag (Node);
   begin
      if Tag = No_Symbol then
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

   ------------------------------
   -- Print_Theory_Declaration --
   ------------------------------

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
      Print_List (+Get_Includes (Node), Separator => "", Newline => False);
      NL (O);
      Print_List (+Get_Declarations (Node), Separator => "", Newline => True);
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

   -------------------
   -- Print_Trigger --
   -------------------

   procedure Print_Trigger (Node : W_Trigger_Id)
   is
      Terms    : constant W_Expr_OList := Get_Terms (Node);
   begin
      Print_List (+Terms);
   end Print_Trigger;

   --------------------
   -- Print_Triggers --
   --------------------

   procedure Print_Triggers (Node : W_Triggers_Id)
   is
      Triggers : constant W_Trigger_List := Get_Triggers (Node);
   begin
      P (O, "[");
      Print_List (+Triggers, Separator => " | ");
      P (O, "]");
   end Print_Triggers;

   ---------------------
   -- Print_Try_Block --
   ---------------------

   procedure Print_Try_Block (Node : W_Try_Block_Id) is
   begin
      PL (O, "try");
      Relative_Indent (O, 1);
      Print_Node (+Get_Prog (Node));
      Relative_Indent (O, -1);
      NL (O);
      PL (O, "with");
      Relative_Indent (O, 1);
      Print_List (+Get_Handler (Node), Separator => "| ", Newline => True);
      Relative_Indent (O, -1);
      NL (O);
      P (O, "end");
   end Print_Try_Block;

   ----------------
   -- Print_Type --
   ----------------

   procedure Print_Type (Node : W_Type_Id)
   is
      Base_Type : constant EW_Type := Get_Type_Kind (Node);
      Name      : constant W_Name_Id := Get_Name (Node);
   begin
      if Present (Name) then
         Print_Node (+Name);
      elsif Base_Type = EW_Abstract then
         declare
            N : constant Node_Id := Get_Ada_Node (+Node);
         begin
            pragma Assert (Present (N));
            P (O, Capitalize_First (Full_Name (N)));
            P (O, ".");
            P (O, Short_Name (N));
         end;
      else
         P (O, Base_Type);
      end if;
      if Get_Is_Mutable (Node) then
         P (O, "__ref");
      end if;
   end Print_Type;

   ---------------------
   -- Print_Type_Decl --
   ---------------------

   procedure Print_Type_Decl (Node : W_Type_Decl_Id) is
      use Why_Node_Lists;

      Args       : constant List := Get_List (+Get_Args (Node));
      Position   : Cursor := First (Args);
      Name       : constant W_Name_Id := Get_Name (Node);
      Definition : constant W_Type_Definition_Id := Get_Definition (Node);
   begin
      P (O, "type ");

      Print_Node (+Name);

      P (O, " ");

      P (O, Get_Labels (Node));

      if Position /= No_Element then
         P (O, "(");

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

         P (O, ") ");
      end if;

      if Definition /= Why_Empty then
         P (O, "=");
         NL (O);
         Relative_Indent (O, 1);
         Print_Node (+Definition);
         Relative_Indent (O, -1);
      end if;
      NL (O);
   end Print_Type_Decl;

   -----------------------------
   -- Print_Universal_Quantif --
   -----------------------------

   procedure Print_Universal_Quantif (Node   : W_Universal_Quantif_Id) is
      Variables       : constant W_Identifier_List := Get_Variables (Node);
      Labels          : constant Symbol_Set := Get_Labels (Node);
      Var_Type        : constant W_Type_Id := Get_Var_Type (Node);
      Triggers        : constant W_Triggers_OId := Get_Triggers (Node);
      Pred            : constant W_Pred_Id := Get_Pred (Node);
      Forall_Sequence : constant Boolean :=
        Get_Kind (+Pred) = W_Universal_Quantif;
      use Why_Node_Lists;
   begin
      P (O, "(");
      P (O, "forall ");
      Print_List (List_Id     => +Variables,
                  Callback    => Print_Node'Access,
                  Separator   => " ",
                  Newline     => False,
                  Loc         => True);

      --  Labels generated for foralls binding several variables are always
      --  faulty because the label is on the forall not on the variables. If we
      --  have several variables, they were introduced by gnat2why and do not
      --  come from source, so we dont want to label them for counterexamples.
      --  Even if one of the variables in question is from source we have no
      --  way to know on which variable is the label.
      if Length (Get_List (+Variables)) <= 1
        and Comes_From_Source (Get_Ada_Node (+Node))
      then
         P (O, " ");
         P (O, Labels, As_Labels => True);
      end if;
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

   ----------------------
   -- Print_While_Loop --
   ----------------------

   procedure Print_While_Loop (Node : W_While_Loop_Id) is

      use Why_Node_Lists;

      Condition    : constant W_Prog_Id := Get_Condition (Node);
      Invs         : constant List := Get_List (+Get_Invariants (Node));
      Loop_Content : constant W_Prog_Id := Get_Loop_Content (Node);

   begin
      P (O, "while ");
      Print_Node (+Condition);
      PL (O, " do");
      Relative_Indent (O, 1);

      if not Invs.Is_Empty then
         for Inv of Invs loop
            P (O, "invariant ");
            PL (O, "{ ");
            Relative_Indent (O, 1);
            Print_Node (+Inv);
            NL (O);
            Relative_Indent (O, -1);
            P (O, " }");
            NL (O);
         end loop;
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
