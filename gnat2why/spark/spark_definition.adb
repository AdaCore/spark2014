------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      S P A R K _ D E F I N I T I O N                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                      Copyright (C) 2011-2014, AdaCore                    --
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

with Ada.Directories;
with Ada.Text_IO;                        use Ada.Text_IO;

with Atree;                              use Atree;
with Einfo;                              use Einfo;
with Elists;                             use Elists;
with Errout;                             use Errout;
with Namet;                              use Namet;
with Nlists;                             use Nlists;
with Opt;                                use Opt;
with Sem_Prag;                           use Sem_Prag;
with Sem_Util;                           use Sem_Util;
with Sem_Ch12;                           use Sem_Ch12;
with Sinfo;                              use Sinfo;
with Sinput;                             use Sinput;
with Snames;                             use Snames;
with Stand;                              use Stand;
with Uintp;                              use Uintp;
with Aspects;                            use Aspects;
with Urealp;                             use Urealp;

with VC_Kinds;

with SPARK_Frame_Conditions;             use SPARK_Frame_Conditions;
with SPARK_Util;                         use SPARK_Util;

with Gnat2Why_Args;

--  with Output; use Output;
--  with Treepr; use Treepr;

package body SPARK_Definition is

   -----------------------------------------
   -- Marking of Entities in SPARK or Not --
   -----------------------------------------

   --  This pass detects which entities are in SPARK and which are not, based
   --  on the presence of SPARK_Mode pragmas in the source, and the violations
   --  of SPARK restrictions. Entities that are not in SPARK may still be
   --  translated in Why, although differently than entities in SPARK
   --  (variables not in SPARK are still declared in case they appear in Global
   --  contracts).

   --  As definitions of entities may be recursive, this pass follows
   --  references to entities not yet marked to decide whether they are in
   --  SPARK or not. We remember which entities are being marked, to avoid
   --  looping. So an entity may be marked at the point where it is declared,
   --  or at some previous point, because it was referenced from another
   --  entity. (This is specially needed for Itypes and class-wide types, which
   --  may not have an explicit declaration, or one that is attached to the
   --  AST.)

   --  Any violation of SPARK rules results in the current toplevel subprogram
   --  (unit subprogram, or subprogram only contained in packages all the
   --  way to the unit level) to be not in SPARK, as well as everything it
   --  defines locally.

   --  An error is raised if an entity that has a corresponding SPARK_Mode
   --  pragma of On is determined to be not in SPARK.

   --  Each entity is added to the list of entities Entity_List. The
   --  translation will depend on the status (in SPARK or not) of each entity,
   --  and on where the entity is declared (in the current unit or not).

   --  A subprogram spec can be in SPARK even if its body is not in SPARK.

   --  Except for private types and deferred constants, a unique entity is used
   --  for multiple views of the same entity. For example, the entity attached
   --  to a subprogram body or a body stub is not used.

   --  Private types are always in SPARK (except currently record (sub)type
   --  with private part), even if the underlying type is not in SPARK. This
   --  allows operations which do not depend on the underlying type to be in
   --  SPARK, which is the case in client code that does not have access to the
   --  underlying type. Since only the partial view of a private type is used
   --  in the AST (except at the point of declaration of the full view), even
   --  when visibility over the full view is needed, the nodes that need this
   --  full view are treated specially, so that they are in SPARK only if the
   --  most underlying type is in SPARK. This most underlying type is the last
   --  type obtained by taking:
   --  . for a private type, its underlying type
   --  . for a record subtype, its base type
   --  . for all other types, itself
   --  until reaching a non-private type that is not a record subtype.

   --  Partial views of deferred constants may be in SPARK even if their full
   --  view is not in SPARK. This is the case if the type of the constant is
   --  in SPARK, while its initializing expression is not.

   -------------------------------------
   -- Adding Entities for Translation --
   -------------------------------------

   Current_SPARK_Pragma : Node_Id;
   --  The current applicable SPARK_Mode pragma, if any, to reference in error
   --  messages when a violation is encountered.

   Violation_Detected : Boolean;
   --  Set to True when a violation is detected

   Inside_Loop : Boolean;
   --  Set to True when traversing a loop. This is used to detect which
   --  entities are defined in loops, which may require a special
   --  translation. Those entities are stored in Loop_Entity_Set.

   Inside_Actions : Boolean;
   --  Set to True when traversing actions (statements introduced by the
   --  compiler inside expressions), which require a special translation.
   --  Those entities are stored in Actions_Entity_Set.

   procedure Initialize;
   procedure Initialize is
   begin
      Current_SPARK_Pragma := Empty;
      Violation_Detected := False;
      Inside_Loop := False;
      Inside_Actions := False;
   end Initialize;

   function SPARK_Pragma_Is (Mode : Opt.SPARK_Mode_Type) return Boolean;
   --  Returns whether Current_SPARK_Pragma is not Empty, and corresponds to
   --  the given Mode.

   function SPARK_Pragma_Is (Mode : Opt.SPARK_Mode_Type) return Boolean is
     (Present (Current_SPARK_Pragma)
       and then Get_SPARK_Mode_From_Pragma (Current_SPARK_Pragma) = Mode);

   --  There are two possibilities when marking an entity, depending on whether
   --  this is in the context of a toplevel subprogram body or not. In the
   --  first case, violations are directly attached to the toplevel subprogram
   --  entity, and local entities are added or not as a whole, after the
   --  subprogram body has been fully marked. In the second case, violations
   --  are attached to the entity itself, which is directly added to the lists
   --  for translation after marking.

   Entities_In_SPARK : Node_Sets.Set;
   --  Entities in SPARK. An entity is inserted in this set if, after marking,
   --  no violations where attached to the corresponding scope. Standard
   --  entities are individually added to this set.

   Specs_In_SPARK    : Node_Sets.Set;
   --  Subprograms and packages whose spec is marked in SPARK

   Bodies_In_SPARK   : Node_Sets.Set;
   --  Subprograms and packages whose body is marked in SPARK

   function Entity_In_SPARK (E : Entity_Id) return Boolean is
     (Entities_In_SPARK.Contains (E));

   function Entity_Spec_In_SPARK (E : Entity_Id) return Boolean is
     (Specs_In_SPARK.Contains (E));

   function Entity_Body_In_SPARK (E : Entity_Id) return Boolean is
     (Bodies_In_SPARK.Contains (E));

   ----------------------
   -- SPARK Violations --
   ----------------------

   procedure Mark_Violation
     (Msg           : String;
      N             : Node_Id;
      SRM_Reference : String := "");
   --  Mark node N as a violation of SPARK. An error message is issued if
   --  current SPARK_Mode is On, which points to the current SPARK_Mode
   --  pragma/aspect. If SRM_Reference is set, the reference to the SRM
   --  is appended to the error message.

   procedure Mark_Violation
     (N    : Node_Id;
      From : Entity_Id);
   --  Mark node N as a violation of SPARK, due to the use of entity From which
   --  is not in SPARK. An error message is issued if current SPARK_Mode is On.

   --------------------
   -- Mark_Violation --
   --------------------

   procedure Mark_Violation
     (Msg           : String;
      N             : Node_Id;
      SRM_Reference : String := "") is
   begin
      --  Flag the violation, so that the current entity is marked accordingly

      Violation_Detected := True;

      --  If SPARK_Mode is On, raise an error

      if SPARK_Pragma_Is (Opt.On) then

         if SRM_Reference /= "" then
            Error_Msg_F
              (Msg & " is not allowed in SPARK (" & SRM_Reference & ")", N);
         else
            Error_Msg_F (Msg & " is not allowed in SPARK", N);
         end if;

         Error_Msg_Sloc := Sloc (Current_SPARK_Pragma);

         if From_Aspect_Specification (Current_SPARK_Pragma) then
            Error_Msg_F ("\\violation of aspect SPARK_Mode #", N);
         else
            Error_Msg_F ("\\violation of pragma SPARK_Mode #", N);
         end if;
      end if;
   end Mark_Violation;

   procedure Mark_Violation
     (N    : Node_Id;
      From : Entity_Id)
   is
   begin
      --  Flag the violation, so that the current entity is marked accordingly

      Violation_Detected := True;

      --  If SPARK_Mode is On, raise an error

      if SPARK_Pragma_Is (Opt.On) then
         Error_Msg_FE ("& is not allowed in SPARK", N, From);
         Error_Msg_Sloc := Sloc (Current_SPARK_Pragma);

         if From_Aspect_Specification (Current_SPARK_Pragma) then
            Error_Msg_F ("\\violation of aspect SPARK_Mode #", N);
         else
            Error_Msg_F ("\\violation of pragma SPARK_Mode #", N);
         end if;
      end if;
   end Mark_Violation;

   ------------------------------
   -- Output SPARK Information --
   ------------------------------

   procedure Generate_Output_In_Out_SPARK (Id : Entity_Id);
   --  Produce a line in output file for subprogram or package Id, in JSON
   --  format, with following interface:

   --   { name  : string,          name of the subprogram / package
   --     file  : string,          file name of the spec
   --     line  : int,             line of the spec
   --     spark : string           spec/body is in SPARK or not
   --   }

   --  Field "spark" takes value in "spec", "all" or "no" to denote
   --  respectively that only the spec is in SPARK, both spec/body are in SPARK
   --  (or spec is in SPARK for a package without body), or the spec is not in
   --  SPARK.

   Output_File : Ada.Text_IO.File_Type;
   --  <file>.alfa in which this pass generates information about subprograms
   --  in SPARK and subprograms not in SPARK.

   First_Entry : Boolean := True;
   --  Global variable used to decide whether a separator needs to be printed
   --  between records in the JSON output

   -------------------
   -- After_Marking --
   -------------------

   procedure After_Marking is
   begin
      Put_Line (Output_File, "]");
      Close (Output_File);
   end After_Marking;

   --------------------
   -- Before_Marking --
   --------------------

   procedure Before_Marking (Basename : String) is
   begin
      Create (Output_File, Out_File,
              Ada.Directories.Compose (Name      => Basename,
                                       Extension => VC_Kinds.SPARK_Suffix));
      Put_Line (Output_File, "[");
   end Before_Marking;

   ----------------------------------
   -- Generate_Output_In_Out_SPARK --
   ----------------------------------

   procedure Generate_Output_In_Out_SPARK (Id : Entity_Id) is
      SPARK_Status : constant String :=
        (if Entity_Body_In_SPARK (Id) then "all"
         elsif Entity_Spec_In_SPARK (Id) then
             (if Ekind (Id) = E_Package
                   and then
                 No (Get_Package_Body (Id))
              then "all" else "spec")
         else "no");
      Line_Num     : constant String :=
        Get_Logical_Line_Number (Sloc (Id))'Img;

   begin
      --  Only add infomation for Id if analysis is requested for that
      --  subprogram or package. Then, absence of errors in flow and warnings
      --  in proof for that subprogram/package can be interpreted as correct
      --  flow analysis or proof of that entity.

      if Analysis_Requested (Id) then
         if First_Entry then
            First_Entry := False;
         else
            Put (Output_File, ", ");
         end if;
         Put_Line
           (Output_File,
            "{ ""name"" : """ & Subprogram_Full_Source_Name (Id) & """, " &
              """file"" :""" & File_Name (Sloc (Id)) & """, " &
              """line"" : " & Line_Num & ", " &
              """spark"" : """ & SPARK_Status & """ }");
      end if;
   end Generate_Output_In_Out_SPARK;

   ----------------------------------
   -- Recursive Marking of the AST --
   ----------------------------------

   procedure Mark (N : Node_Id);
   --  Generic procedure for marking code

   function In_SPARK (E : Entity_Id) return Boolean;
   --  Returns whether the entity E is in SPARK. If not already done, it
   --  computes this information by calling Mark_Entity.

   --  Marking of entities

   procedure Mark_Entity (E : Entity_Id);
   --  Push entity E on the stack, mark E, and pop E from the stack. Always
   --  adds E to the set of Entity_Set as a result. If no violation was
   --  detected, E is added to the Entities_In_SPARK.

   --  Marking of declarations

   procedure Mark_Number_Declaration          (N : Node_Id);
   procedure Mark_Object_Declaration          (N : Node_Id);
   procedure Mark_Package_Body                (N : Node_Id);
   procedure Mark_Package_Declaration         (N : Node_Id);
   procedure Mark_Subprogram_Body             (N : Node_Id);
   procedure Mark_Subprogram_Declaration      (N : Node_Id);
   --  N is either a subprogram declaration node, or a subprogram body node
   --  for those subprograms which do not have a prior declaration (not
   --  counting a stub as a declaration).

   --  Special treatment for marking some kinds of nodes

   procedure Mark_Attribute_Reference         (N : Node_Id);
   procedure Mark_Binary_Op                   (N : Node_Id);
   procedure Mark_Call                        (N : Node_Id);
   procedure Mark_Component_Declaration       (N : Node_Id);
   procedure Mark_Handled_Statements          (N : Node_Id);
   procedure Mark_Identifier_Or_Expanded_Name (N : Node_Id);
   procedure Mark_If_Expression               (N : Node_Id);
   procedure Mark_If_Statement                (N : Node_Id);
   procedure Mark_Iteration_Scheme            (N : Node_Id);
   procedure Mark_Pragma                      (N : Node_Id);
   procedure Mark_Simple_Return_Statement     (N : Node_Id);
   procedure Mark_Extended_Return_Statement   (N : Node_Id);
   procedure Mark_Subtype_Indication          (N : Node_Id);
   procedure Mark_Unary_Op                    (N : Node_Id);

   procedure Mark_Actions (N : Node_Id; L : List_Id);
   --  Mark a possibly null list of actions L from expression N. It should be
   --  called before the expression to which the actions apply is marked, so
   --  that declarations of constants in actions are possibly marked in SPARK.

   procedure Mark_List (L : List_Id);
   --  Call Mark on all nodes in list L

   procedure Mark_Most_Underlying_Type_In_SPARK (Id : Entity_Id; N : Node_Id);
   --  The most underlying type for type Id should be in SPARK, otherwise mark
   --  node N as not in SPARK.

   --------------
   -- In_SPARK --
   --------------

   function In_SPARK (E : Entity_Id) return Boolean is
   begin
      Mark_Entity (E);
      return Entities_In_SPARK.Contains (E);
   end In_SPARK;

   -----------------
   -- Mark_Entity --
   -----------------

   procedure Mark_Entity (E : Entity_Id) is

      --  Subprograms for marking specific entities. These are defined locally
      --  so that they cannot be called from other marking subprograms, which
      --  should call Mark_Entity instead.

      procedure Mark_Parameter_Entity (E : Entity_Id);
      --  E is a subprogram or a loop parameter

      procedure Mark_Number_Entity     (E : Entity_Id);
      procedure Mark_Object_Entity     (E : Entity_Id);
      procedure Mark_Package_Entity    (E : Entity_Id);
      procedure Mark_Subprogram_Entity (E : Entity_Id);
      procedure Mark_Type_Entity       (E : Entity_Id);

      ------------------------
      -- Mark_Number_Entity --
      ------------------------

      procedure Mark_Number_Entity (E : Entity_Id) is
         N    : constant Node_Id   := Parent (E);
         Expr : constant Node_Id   := Expression (N);
         T    : constant Entity_Id := Etype (E);
      begin
         if not In_SPARK (T) then
            Mark_Violation (N, From => T);
         end if;

         if Present (Expr) then
            Mark (Expr);
         end if;
      end Mark_Number_Entity;

      ------------------------
      -- Mark_Object_Entity --
      ------------------------

      procedure Mark_Object_Entity (E : Entity_Id) is
         N    : constant Node_Id   := Parent (E);
         Def  : constant Node_Id   := Object_Definition (N);
         Expr : constant Node_Id   := Expression (N);
         T    : constant Entity_Id := Etype (E);
         Sub  : constant Entity_Id := Actual_Subtype (E);

      begin
         --  all objects should be registered in the object map of
         --  SPARK_Frame_Conditions. See the documentation there.

         Register_Object_Entity (E);

         --  The object is in SPARK if-and-only-if its type is in SPARK, it
         --  is not aliased, and its initialization expression, if any, is
         --  in SPARK.

         if not In_SPARK (T) then
            Mark_Violation (Def, From => T);
         end if;

         if Present (Sub)
           and then not In_SPARK (Sub)
         then
            Mark_Violation (Def, From => Sub);
         end if;

         if Aliased_Present (N) then
            Mark_Violation ("ALIASED", N);
         end if;

         if Present (Expr) then
            Mark (Expr);
         end if;
      end Mark_Object_Entity;

      -------------------------
      -- Mark_Package_Entity --
      -------------------------

      procedure Mark_Package_Entity (E : Entity_Id) is

         procedure Declare_In_Package_With_External_Axioms (Decls : List_Id);
         --  Mark types, subprograms and objects from a package with external
         --  axioms.

         procedure Mark_Generic_Parameters_External_Axioms (Assoc : List_Id);
         --  Mark actual parameters of a package with external axioms.

         ---------------------------------------------
         -- Declare_In_Package_With_External_Axioms --
         ---------------------------------------------

         procedure Declare_In_Package_With_External_Axioms (Decls : List_Id) is
            Decl : Node_Id;
            Id   : Entity_Id;
         begin
            Decl := First (Decls);

            --  Mark formals of the generic if any:
            --  The mapping nodes are all nodes starting from the top of the
            --  visible declarations upto the first source node (detectable by
            --  Comes_From_Source (...)).

            while Present (Decl) and then not Comes_From_Source (Decl) loop
               if Nkind (Decl) in N_Full_Type_Declaration         |
                                  N_Private_Type_Declaration      |
                                  N_Private_Extension_Declaration |
                                  N_Subtype_Declaration           |
                                  N_Subprogram_Declaration        |
                                  N_Object_Declaration
               then
                  Id := Defining_Entity (Decl);
                  if Ekind (Id) in Type_Kind then
                        Mark_Entity (Id);
                  elsif Ekind (Id) in Object_Kind | Subprogram_Kind then
                     Entity_Set.Include (Id);
                     Entities_In_SPARK.Include (Id);
                  end if;
               end if;
               Next (Decl);
            end loop;

            while Present (Decl) loop
               if Nkind (Decl) in N_Package_Declaration then

                  --  Mark elements of any sub-package

                  Declare_In_Package_With_External_Axioms
                    (Visible_Declarations (Specification (Decl)));
               elsif Nkind (Decl) in N_Full_Type_Declaration         |
                                  N_Private_Type_Declaration      |
                                  N_Private_Extension_Declaration |
                                  N_Subtype_Declaration           |
                                  N_Subprogram_Declaration        |
                                  N_Object_Declaration
               then
                  Id := Defining_Entity (Decl);

                  if Ekind (Id) in Type_Kind then
                     if not Is_Hidden (Id) then

                        --  Should only mark types that are public or formals
                        --  of the generic. Others are simply ignored.

                        Mark_Entity (Id);
                     end if;
                  elsif Ekind (Id) in Object_Kind | Subprogram_Kind then
                     Entity_Set.Include (Id);
                     Entities_In_SPARK.Include (Id);
                  end if;
               end if;

               Next (Decl);
            end loop;
         end Declare_In_Package_With_External_Axioms;

         ---------------------------------------------
         -- Mark_Generic_Parameters_External_Axioms --
         ---------------------------------------------

         procedure Mark_Generic_Parameters_External_Axioms (Assoc : List_Id) is
            Cur_Assoc : Node_Id := First (Assoc);
         begin
            while Present (Cur_Assoc) loop
               declare
                  Actual : constant Node_Id :=
                    Explicit_Generic_Actual_Parameter (Cur_Assoc);
                  EActual : constant Entity_Id :=
                    (if Ekind (Entity (Actual)) = E_Function then
                        Get_Renamed_Entity (Entity (Actual))
                     else Entity (Actual));

               begin
                  --  Operators as actual of packages with external axioms are
                  --  not supported yet.

                  if Ekind (EActual) = E_Operator then
                     Error_Msg_N
                       ("operator cannot be used as a formal parameter",
                        Actual);
                     Error_Msg_N
                       ("\\package is defined with external axiomatization",
                        Actual);
                     Error_Msg_N
                       ("\\consider using a wrapper instead", Actual);
                  end if;

                  --  Mark the entity of the actual

                  Mark_Entity (EActual);
               end;

               Next (Cur_Assoc);
            end loop;
         end Mark_Generic_Parameters_External_Axioms;

         Vis_Decls : constant List_Id :=
           Visible_Declarations (Get_Package_Spec (E));

      --  Start of Mark_Package_Entity

      begin
         --  Do not analyze specs for instantiations of the formal containers.
         --  Only mark types in SPARK or not, and mark all subprograms in
         --  SPARK, but none should be scheduled for translation into Why3.

         if Entity_In_External_Axioms (E) then

            --  If Id is a package instance, mark its actual parameters

            declare
               G_Parent : constant Node_Id :=
                 Generic_Parent (Get_Package_Spec (E));
            begin
               if Present (G_Parent) then
                  Mark_Generic_Parameters_External_Axioms
                    (Generic_Associations
                       (Get_Package_Instantiation_Node (E)));
               end if;
            end;

            --  Explicitly add the package declaration to the entities to
            --  translate into Why3.

            Entity_List.Append (E);

            --  Mark types and subprograms from packages with external axioms
            --  as in SPARK or not.

            Declare_In_Package_With_External_Axioms (Vis_Decls);
         end if;
      end Mark_Package_Entity;

      ---------------------------
      -- Mark_Parameter_Entity --
      ---------------------------

      procedure Mark_Parameter_Entity (E : Entity_Id) is
         T   : constant Entity_Id := Etype (E);

         --  Actual_Subtype is only defined for subprogram parameters, not on
         --  loop parameters.

         Sub : constant Entity_Id :=
           (if Is_Formal (E) then Actual_Subtype (E) else Empty);

      begin
         --  all objects should be registered in the object map of
         --  SPARK_Frame_Conditions. See the documentation there.

         Register_Object_Entity (E);

         if not In_SPARK (T) then
            Mark_Violation (E, From => T);
         end if;

         if Present (Sub)
           and then not In_SPARK (Sub)
         then
            Mark_Violation (E, From => Sub);
         end if;
      end Mark_Parameter_Entity;

      ----------------------------
      -- Mark_Subprogram_Entity --
      ----------------------------

      procedure Mark_Subprogram_Entity (E : Entity_Id) is

         procedure Mark_Function_Specification (N : Node_Id);
         --  Mark violations related to impure functions

         procedure Mark_Subprogram_Specification (N : Node_Id);
         --  Mark violations related to parameters, result and contract

         ---------------------------------
         -- Mark_Function_Specification --
         ---------------------------------

         procedure Mark_Function_Specification (N : Node_Id) is
            Id       : constant Entity_Id := Defining_Entity (N);
            Params   : constant List_Id   := Parameter_Specifications (N);
            Param    : Node_Id;
            Param_Id : Entity_Id;

         begin
            if Is_Non_Empty_List (Params) then
               Param := First (Params);
               while Present (Param) loop
                  Param_Id := Defining_Identifier (Param);

                  case Ekind (Param_Id) is
                     when E_Out_Parameter =>
                        Mark_Violation ("function with OUT parameter", Id);
                        return;

                     when E_In_Out_Parameter =>
                        Mark_Violation ("function with IN OUT parameter", Id);
                        return;

                     when others =>
                        null;
                  end case;

                  Next (Param);
               end loop;
            end if;
         end Mark_Function_Specification;

         -----------------------------------
         -- Mark_Subprogram_Specification --
         -----------------------------------

         procedure Mark_Subprogram_Specification (N : Node_Id) is
            Id         : constant Entity_Id := Defining_Entity (N);
            Formals    : constant List_Id   := Parameter_Specifications (N);
            Param_Spec : Node_Id;
            Formal     : Entity_Id;

         begin
            if Ekind (Id) = E_Function then
               Mark_Function_Specification (N);
            end if;

            if Present (Formals) then
               Param_Spec := First (Formals);
               while Present (Param_Spec) loop
                  Formal := Defining_Identifier (Param_Spec);
                  if not In_SPARK (Etype (Formal)) then
                     Mark_Violation (E, From => Etype (Formal));
                  end if;
                  Mark_Entity (Formal);
                  Next (Param_Spec);
               end loop;
            end if;

            --  If the result type of a subprogram is not in SPARK, then the
            --  subprogram is not in SPARK.

            if Nkind (N) = N_Function_Specification
              and then not In_SPARK (Etype (Id))
            then
               Mark_Violation (Result_Definition (N), From => Etype (Id));
            end if;
         end Mark_Subprogram_Specification;

         Prag : Node_Id;
         Expr : Node_Id;

      --  Start of Mark_Subprogram_Entity

      begin

         Mark_Subprogram_Specification (Get_Subprogram_Spec (E));

         Prag := Pre_Post_Conditions (Contract (E));
         while Present (Prag) loop
            Expr :=
              Get_Pragma_Arg (First (Pragma_Argument_Associations (Prag)));
            Mark (Expr);
            Prag := Next_Pragma (Prag);
         end loop;

         Prag := Get_Subprogram_Contract_Cases (E);
         if Present (Prag) then
            declare
               Aggr           : constant Node_Id :=
                 Expression (First (Pragma_Argument_Associations (Prag)));
               Case_Guard     : Node_Id;
               Conseq         : Node_Id;
               Contract_Case  : Node_Id;
            begin
               Contract_Case := First (Component_Associations (Aggr));
               while Present (Contract_Case) loop
                  Case_Guard := First (Choices (Contract_Case));
                  Conseq     := Expression (Contract_Case);

                  Mark (Case_Guard);
                  Mark (Conseq);

                  Next (Contract_Case);
               end loop;
            end;
         end if;
      end Mark_Subprogram_Entity;

      ----------------------
      -- Mark_Type_Entity --
      ----------------------

      procedure Mark_Type_Entity (E : Entity_Id) is

         function Is_Private_Entity_Mode_Off (E : Entity_Id) return Boolean;
         --  return True if E is declared in a private part with
         --  SPARK_Mode => Off;

         function Is_Private_Entity_Mode_Off (E : Entity_Id) return Boolean
         is
            Decl : constant Node_Id :=
              (if No (Parent (Parent (E)))
               and then Is_Itype (E) then
                    Associated_Node_For_Itype (E)
               else Parent (E));
            Pack_Decl : constant Node_Id := Parent (Parent (Decl));
         begin
            pragma Assert
              (Nkind (Pack_Decl) = N_Package_Declaration);

            return
              Present (SPARK_Aux_Pragma (Defining_Entity (Pack_Decl)))
              and then Get_SPARK_Mode_From_Pragma
                (SPARK_Aux_Pragma (Defining_Entity (Pack_Decl))) = Off;
         end Is_Private_Entity_Mode_Off;

      begin

         --  For types in external axioms, mark the package entity.

         if Entity_In_External_Axioms (E) then
            Mark_Entity (Axiomatized_Package_For_Entity (E));
         end if;

         --  The base type or original type should be marked before the current
         --  type. We also protect ourselves against the case where the Etype
         --  of a full view points to the partial view.

         if Etype (E) /= E and then
           (Underlying_Type (Etype (E)) /= E)
         then
            Mark_Entity (Etype (E));
         end if;

         --  Type declarations may refer to private types whose full view has
         --  not been declared yet. However, it is this full view which may
         --  define the type in Why3, if it happens to be in SPARK. Hence the
         --  need to define it now, so that it is available for the current
         --  type definition. So we start here with marking all needed types
         --  if not already marked.

         case Ekind (E) is
         when Array_Kind =>
            declare
               Component_Typ : constant Node_Id := Component_Type (E);
               Index         : Node_Id := First_Index (E);
            begin
               if Present (Component_Typ) then
                  Mark_Entity (Component_Typ);
               end if;

               while Present (Index) loop
                  Mark_Entity (Etype (Index));
                  Next_Index (Index);
               end loop;
            end;

         --  Itypes may be generated by the frontend for component types.
         --  Mark them here, to avoid multiple definitions of the same type
         --  in multiple client packages.

         when E_Record_Type | E_Record_Subtype =>
            declare
               Field : Node_Id := First_Entity (E);
            begin
               while Present (Field) loop
                  if Ekind (Field) in Object_Kind then
                     Mark_Entity (Etype (Field));
                  end if;
                  Next_Entity (Field);
               end loop;
            end;

         --  In the case of a package instantiation of a generic, the full view
         --  of a private type may not have a corresponding declaration. It is
         --  marked here.

         when Private_Kind =>

            --  When a private type is defined in a package with external
            --  axioms or in a private part with SPARK_Mode => Off, we do not
            --  consider the underlying type.
            --  If a private type is based on a type where the underlying type
            --  was not considered or not in SPARK, we don't consider its
            --  underlying type.

            if (Etype (E) = E and then
                  (Entity_In_External_Axioms (E) or else
                   Is_Private_Entity_Mode_Off (E))) or else
              (Etype (E) /= E and then
               Entity_In_SPARK (Etype (E)) and then
                 not Entity_In_SPARK (Underlying_Type (Etype (E))))
            then
               Entity_Set.Insert (Underlying_Type (E));
            else
               Mark_Entity (Underlying_Type (E));
            end if;
         when others =>
            null;
         end case;

         --  Now mark the type itself

         if Is_Tagged_Type (E) then
            Mark_Violation ("tagged type", E);
         end if;

         if Has_Invariants (E) then
            Mark_Violation ("type invariant", E);
         end if;

         if Has_Predicates (E) then
            if No (Static_Predicate (E)) then
               Mark_Violation ("dynamic type predicate", E);
            else
               declare
                  Pred : Node_Id := First (Static_Predicate (E));
               begin
                  while Present (Pred) loop
                     Mark (Pred);
                     Next (Pred);
                  end loop;
               end;
            end if;
         end if;

         --  Detect if the type has partial default initialization

         if SPARK_Util.Default_Initialization (E) = Mixed_Initialization then
            Mark_Violation ("type with partial default initialization",
                            E,
                            SRM_Reference => "SPARK RM 3.8(1)");
         end if;

         case Ekind (E) is
         when Array_Kind =>
            declare
               Component_Typ : constant Node_Id := Component_Type (E);
               Index         : Node_Id := First_Index (E);

            begin
               if Positive (Number_Dimensions (E)) > Max_Array_Dimensions then
                  Violation_Detected := True;
                  if SPARK_Pragma_Is (Opt.On) then
                     Error_Msg_Node_1 := E;
                     Error_Msg_Uint_1 := UI_From_Int (Number_Dimensions (E));
                     Error_Msg_N ("} of dimension ^ is not yet supported", E);
                  end if;
               end if;

               --  Check that all index types are in SPARK

               while Present (Index) loop
                  if not In_SPARK (Etype (Index)) then
                     Mark_Violation (E, From => Etype (Index));
                  end if;
                  Next_Index (Index);
               end loop;

               --  Access definition for component type is not in SPARK

               if No (Component_Typ) then
                  Mark_Violation ("access type", E);
               end if;

               --  Check that component type is in SPARK.

               if not In_SPARK (Component_Typ) then
                  Mark_Violation (E, From => Component_Typ);
               end if;
            end;

         --  Discrete and floating-point types are always in SPARK

         when Integer_Kind | Float_Kind | Enumeration_Kind =>
            null;

         when Fixed_Point_Kind =>
            declare
               function Only_Factor_Is
                 (Num    : Uint;
                  Factor : Uint) return Boolean
               with Pre => UI_Gt (Num, Uint_0)
                 and then UI_Gt (Factor, Uint_0);
               --  Returns True if Num is a power of Factor

               --------------------
               -- Only_Factor_Is --
               --------------------

               function Only_Factor_Is
                 (Num    : Uint;
                  Factor : Uint) return Boolean
               is
                  N : Uint := Num;
               begin
                  while N /= Uint_1 loop
                     if UI_Rem (N, Factor) /= Uint_0 then
                        return False;
                     end if;
                     N := UI_Div (N, Factor);
                  end loop;

                  return True;
               end Only_Factor_Is;

               Inv_Small : constant Ureal := UR_Div (Uint_1, Small_Value (E));
               Inv_Small_Num : constant Uint := Norm_Num (Inv_Small);
            begin
               if Norm_Den (Inv_Small) = Uint_1
                    and then
                  Inv_Small_Num /= Uint_1
                    and then
                  (Only_Factor_Is (Inv_Small_Num, Uint_2)
                     or else
                   Only_Factor_Is (Inv_Small_Num, Uint_10))
               then
                  null;
               else
                  Violation_Detected := True;
                  if SPARK_Pragma_Is (Opt.On) then
                     Error_Msg_N
                       ("fixed-point type whose small is not a negative power "
                        & "of 2 or 10 is not yet supported", E);
                  end if;
               end if;
            end;

         when E_Record_Type | E_Record_Subtype =>

            if Ekind (E) = E_Record_Subtype
              and then not In_SPARK (Base_Type (E))
            then
               Mark_Violation (E, From => Base_Type (E));
            end if;

            if Is_Interface (E) then
               Mark_Violation ("interface", E);

            else
               declare
                  Field : Node_Id := First_Component_Or_Discriminant (E);
                  Typ   : Entity_Id;

               begin
                  while Present (Field) loop
                     Typ := Etype (Field);

                     if Is_Tag (Field) then
                        Mark_Violation ("tagged type", E);
                     elsif Is_Aliased (Field) then
                        Mark_Violation ("ALIASED", Field);
                     end if;

                     if Ekind (Field) in Object_Kind
                       and then not In_SPARK (Typ)
                     then
                        Mark_Violation (Typ, From => Typ);
                     end if;

                     Next_Component_Or_Discriminant (Field);
                  end loop;
               end;
            end if;

            --  Discriminant renamings are not in SPARK, this is checked here

            declare
               Disc  : Entity_Id := First_Discriminant (E);
               Found : Boolean := False;
            begin
               while Present (Disc) loop
                  if Present (Corresponding_Discriminant (Disc))
                    and then
                      Chars (Disc) /= Chars (Corresponding_Discriminant (Disc))
                  then
                     Found := True;
                  end if;
                  exit when Found;
                  Next_Discriminant (Disc);
               end loop;
               if Found then
                  Mark_Violation ("discriminant renaming", E);
               end if;
            end;

         when E_Class_Wide_Type    |
              E_Class_Wide_Subtype =>
            Mark_Violation ("type definition", E);

         when Access_Kind =>
            Mark_Violation ("access type", E);

         when Concurrent_Kind =>
            Mark_Violation ("tasking", E);

         when Private_Kind =>

            --  Private types that are not a record type or subtype are in
            --  SPARK.

            if Ekind_In (E, E_Record_Type_With_Private,
                         E_Record_Subtype_With_Private)
            then
               Mark_Violation ("type definition", E);
            end if;

            --  Private types may export discriminants. Discriminants with
            --  non-SPARK type should be disallowed here

            declare
               Disc : Entity_Id := First_Discriminant (E);
            begin
               while Present (Disc) loop
                  if not In_SPARK (Etype (Disc)) then
                     Mark_Violation (E, From => Etype (Disc));
                  end if;
                  Next_Discriminant (Disc);
               end loop;
            end;

         when others =>
            raise Program_Error;
         end case;
      end Mark_Type_Entity;

      --  Save whether a violation was previously detected, to restore after
      --  marking this entity.

      Save_Violation_Detected : constant Boolean := Violation_Detected;
      Save_SPARK_Pragma : constant Node_Id := Current_SPARK_Pragma;

   --  Start of Mark_Entity

   begin

      --  ??? predicate_functions ignored for now (MC20-028)

      if Ekind (E) in E_Function | E_Procedure
        and then Is_Predicate_Function (E)
      then
         return;
      end if;

      --  Nothing to do if the entity E was already marked

      if Entity_Set.Contains (E) then
         return;
      end if;

      --  Store entities defines in loops in Loop_Entity_Set

      if Inside_Loop then
         Loop_Entity_Set.Insert (E);
      end if;

      --  Store entities defines in actions in Actions_Entity_Set

      if Inside_Actions then
         Actions_Entity_Set.Insert (E);
      end if;

      --  Types may be marked out of order, because completions of private
      --  types need to be marked at the point of their partial view
      --  declaration, to avoid out-of-order declarations in Why.
      --  Retrieve the appropriate SPARK_Mode pragma before marking.

      if Ekind (E) in Type_Kind then
         declare
            Decl : constant Node_Id :=
              (if No (Parent (Parent (E)))
               and then Is_Itype (E) then
                    Associated_Node_For_Itype (E) else Parent (E));
         begin
            pragma Assert (Present (Parent (Decl)));
            if In_Private_Declarations (Decl) then
               declare
                  Pack_Decl : constant Node_Id := Parent (Parent (Decl));
               begin
                  pragma Assert
                    (Nkind (Pack_Decl) = N_Package_Declaration);

                  Current_SPARK_Pragma :=
                    SPARK_Aux_Pragma (Defining_Entity (Pack_Decl));
               end;

            else
               null;
            end if;
         end;
      end if;

      --  Include entity E in the set of entities marked

      Entity_Set.Insert (E);

      --  If the entity is declared in the scope of SPARK_Mode => Off, then do
      --  not consider whether it could be in SPARK or not.

      if SPARK_Pragma_Is (Opt.Off) then
         return;
      end if;

      --  For recursive references, start with marking the entity in SPARK

      Entities_In_SPARK.Include (E);

      --  Start with no violation being detected

      Violation_Detected := False;

      --  Mark differently each kind of entity

      case Ekind (E) is
         when Type_Kind        => Mark_Type_Entity (E);
         when Subprogram_Kind  => Mark_Subprogram_Entity (E);
         when E_Constant       |
              E_Variable       =>
            begin
               case Nkind (Parent (E)) is
                  when N_Object_Declaration     => Mark_Object_Entity (E);
                  when N_Iterator_Specification => Mark_Parameter_Entity (E);
                  when others                   => raise Program_Error;
               end case;
            end;
         when E_Loop_Parameter |
              Formal_Kind      => Mark_Parameter_Entity (E);
         when Named_Kind       => Mark_Number_Entity (E);
         when E_Package        => Mark_Package_Entity (E);

         --  The identifier of a loop is used to generate the needed exception
         --  declarations in the translation phase.

         when E_Loop           => null;

         --  Mark_Entity is called on all abstract state variables

         when E_Abstract_State => null;

         when others           =>
            Ada.Text_IO.Put_Line ("[Mark_Entity] kind ="
                                  & Entity_Kind'Image (Ekind (E)));
            raise Program_Error;
      end case;

      --  If a violation was detected, remove E from the set of SPARK entities

      if Violation_Detected then
         Entities_In_SPARK.Delete (E);
      end if;

      --  Add entity to appropriate list. Type from packages with external
      --  axioms are handled by a specific mechanism and thus should not be
      --  translated.

      if not Entity_In_External_Axioms (E) then
         Entity_List.Append (E);
      end if;

      --  Update the information that a violation was detected

      Violation_Detected := Save_Violation_Detected;

      --  Restore SPARK_Mode pragma

      Current_SPARK_Pragma := Save_SPARK_Pragma;
   end Mark_Entity;

   ----------
   -- Mark --
   ----------

   procedure Mark (N : Node_Id) is

      -----------------------
      -- Local subprograms --
      -----------------------

      function Is_Update_Aggregate (Aggr : Node_Id) return Boolean;
      --  Detect whether Aggr is an aggregate node modelling 'Update. Returns
      --  false for a normal aggregate.

      function Is_Special_Multidim_Update_Aggr (Aggr : Node_Id) return Boolean;
      --  Detect special case of AST node.
      --  For an 'Update of a multidimensional array, the indexed components
      --    (the expressions (1, 1), (2, 2) and (3, 3) in example
      --     Arr_A2D'Update ((1, 1) => 1,  (2, 2) => 2, (3, 3) => 3,
      --     where Arr_A2D is a two-dimensional array)
      --  are modelled in the AST using an aggregate node which does not have a
      --  a type. An aggregate node is expected to have a type, but this
      --  kind of expression (indexed components) is not, so need to detect
      --  special case here.
      --  Why aren't these kind of nodes Indexed_Components instead?

      -------------------------
      -- Is_Update_Aggregate --
      -------------------------

      function Is_Update_Aggregate (Aggr : Node_Id) return Boolean is
         Result : Boolean := False;
         Par    : Node_Id;
      begin
         if Nkind (Aggr) = N_Aggregate then
            Par := Parent (Aggr);
            if Present (Par)
              and then Nkind (Par) = N_Attribute_Reference
              and then Get_Attribute_Id
                         (Attribute_Name (Par)) = Attribute_Update
            then
               Result := True;
            end if;
         end if;
         return Result;
      end Is_Update_Aggregate;

      -------------------------------------
      -- Is_Special_Multidim_Update_Aggr --
      -------------------------------------

      function Is_Special_Multidim_Update_Aggr (Aggr : Node_Id) return Boolean
      is
         Result : Boolean := False;
         Pref, Par, Grand_Par, Grand_Grand_Par : Node_Id;
      begin
         if Nkind (Aggr) = N_Aggregate then
            Par := Parent (Aggr);
            if Present (Par) then
               Grand_Par := Parent (Par);
               if Present (Grand_Par)
                 and then Is_Update_Aggregate (Grand_Par)
               then
                  Grand_Grand_Par := Parent (Grand_Par);
                  Pref := Prefix (Grand_Grand_Par);
                  if Is_Array_Type (Etype (Pref))
                    and then Number_Dimensions (Etype (Pref)) > 1
                  then
                     Result := True;
                  end if;
               end if;
            end if;
         end if;
         return Result;
      end Is_Special_Multidim_Update_Aggr;

      --  Start of processing for Mark

   begin
      --  If present, the type of N should be in SPARK. This also allows
      --  marking Itypes and class-wide types at their first occurrence
      --  (inside In_SPARK).

      --  The type may be absent on kinds of nodes that should have types,
      --  in very special cases, like the fake aggregate node in a 'Update
      --  attribute_reference, and the fake identifier node for an abstract
      --  state. So we also check that the type is explicitly present.

      if Nkind (N) in N_Has_Etype
        and then Present (Etype (N))
        and then not In_SPARK (Etype (N))
      then
         Mark_Violation (N, From => Etype (N));
      end if;

      --  Dispatch on node kind

      case Nkind (N) is

         when N_Abstract_Subprogram_Declaration =>
            Mark_Violation ("abstract subprogram", N);

         when N_Aggregate =>
            if not Is_Update_Aggregate (N)
              and then not Is_Special_Multidim_Update_Aggr (N)
            then
               if not Aggregate_Is_Fully_Initialized (N) then
                  Mark_Violation ("aggregate not fully defined", N,
                                  SRM_Reference => "SPARK RM 4.3");
               end if;
               Mark_Most_Underlying_Type_In_SPARK (Etype (N), N);
            end if;
            Mark_List (Expressions (N));
            Mark_List (Component_Associations (N));

         when N_Allocator =>
            Mark_Violation ("allocator", N);

         when N_Assignment_Statement =>
            Mark (Name (N));
            Mark (Expression (N));

         when N_Attribute_Reference =>
            Mark_Attribute_Reference (N);

         when N_Binary_Op =>
            Mark_Binary_Op (N);

         when N_Block_Statement =>
            Mark_List (Declarations (N));
            Mark (Handled_Statement_Sequence (N));

         when N_Case_Expression |
              N_Case_Statement  =>
            Mark (Expression (N));
            Mark_List (Alternatives (N));

         when N_Case_Expression_Alternative =>
            Mark_Actions (N, Actions (N));
            Mark (Expression (N));

         when N_Case_Statement_Alternative =>
            Mark_List (Statements (N));

         when N_Code_Statement =>
            Mark_Violation ("code statement", N);

         when N_Component_Association =>
            pragma Assert (No (Loop_Actions (N)));
            Mark_List (Choices (N));

            if Box_Present (N) then
               Mark_Violation ("aggregate not full defined", N,
                               SRM_Reference => "SPARK RM 4.3");
            else
               Mark (Expression (N));
            end if;

         when N_Component_Declaration =>
            Mark_Component_Declaration (N);

         when N_Exception_Declaration          |
              N_Exception_Renaming_Declaration =>
            Mark_Violation ("exception", N);

         when N_Exit_Statement =>
            if Present (Condition (N)) then
               Mark (Condition (N));
            end if;

         when N_Expanded_Name =>
            Mark_Identifier_Or_Expanded_Name (N);

         when N_Explicit_Dereference =>
            Mark_Violation ("explicit dereference", N);

         when N_Extended_Return_Statement =>
            Mark_Extended_Return_Statement (N);

         when N_Extension_Aggregate =>
            Mark_Violation ("extension aggregate", N);

         when N_Free_Statement =>
            Mark_Violation ("free statement", N);

         when N_Function_Call =>
            Mark_Call (N);

         when N_Goto_Statement =>
            Mark_Violation ("goto statement", N);

         when N_Handled_Sequence_Of_Statements =>
            Mark_Handled_Statements (N);

         when N_Identifier =>
            Mark_Identifier_Or_Expanded_Name (N);

         when N_If_Expression =>
            Mark_If_Expression (N);

         when N_If_Statement =>
            Mark_If_Statement (N);

         when N_Indexed_Component =>
            Mark_Most_Underlying_Type_In_SPARK (Etype (Prefix (N)), N);
            Mark (Prefix (N));
            Mark_List (Expressions (N));

         when N_Iterator_Specification =>

            --  Retrieve Iterable aspect specification if any

            declare
               Iterable_Aspect : constant Node_Id :=
                 Find_Aspect (Id => Etype (Name (N)), A => Aspect_Iterable);
            begin

               if Present (Iterable_Aspect) then

--                    if Of_Present (N) then
--                       Violation_Detected := True;
--                       if SPARK_Pragma_Is (Opt.On) then
--                          Error_Msg_N
--                       ("Of quantification on types with Iterable aspect"
--                             & " is not yet supported",
--                             N);
--                       end if;
--                    end if;

                  --  Mark components of the Iterable aggregate

                  declare
                     Iterable_Component_Assoc : constant List_Id :=
                       Component_Associations (Expression
                                               (Iterable_Aspect));
                     Iterable_Field : Node_Id :=
                       First (Iterable_Component_Assoc);

                  begin

                     while Present (Iterable_Field) loop
                        Mark (Expression (Iterable_Field));
                        Next (Iterable_Field);
                     end loop;

                  end;

                  Mark (Name (N));

               else

                  --  if no Iterable aspect is found, raise a violation
                  --  other forms of iteration are not allowed in SPARK

                  Mark_Violation ("iterator specification", N,
                                  SRM_Reference => "SPARK RM 5.5.2");
               end if;
            end;

         when N_Loop_Statement =>
            declare
               Save_Inside_Loop : constant Boolean := Inside_Loop;
            begin
               Inside_Loop := True;

               --  Mark the entity for the loop, which is used in the
               --  translation phase to generate exceptions for this loop.

               Mark_Entity (Entity (Identifier (N)));

               if Present (Iteration_Scheme (N)) then
                  Mark_Iteration_Scheme (Iteration_Scheme (N));
               end if;
               Mark_List (Statements (N));

               Inside_Loop := Save_Inside_Loop;
            end;

         when N_Membership_Test =>
            if Is_Array_Type (Etype (Left_Opnd (N))) then
               Violation_Detected := True;
               if SPARK_Pragma_Is (Opt.On) then
                  Error_Msg_N
                    ("membership test on array values is not yet supported",
                     N);
               end if;
            end if;
            Mark (Left_Opnd (N));
            if Present (Alternatives (N)) then
               Mark_List (Alternatives (N));
            else
               Mark (Right_Opnd (N));
            end if;

         when N_Null =>
            Mark_Violation ("null", N);

         when N_Number_Declaration =>
            Mark_Number_Declaration (N);

         when N_Object_Declaration =>
            declare
               E : constant Entity_Id := Defining_Entity (N);
            begin
               --  Store correspondance from completions of deferred constants,
               --  so that Is_Full_View can be used for dealing correctly with
               --  deferred constants, when the public part of the package is
               --  marked as SPARK_Mode On, and the private part of the package
               --  is marked as SPARK_Mode Off. This is also used later during
               --  generation of Why.

               if Ekind (E) = E_Constant
                 and then Present (Full_View (E))
               then
                  Add_Full_And_Partial_View (Full_View (E), E);
               end if;

               Mark_Object_Declaration (N);
            end;

         when N_Package_Body =>
            Mark_Package_Body (N);

         when N_Package_Body_Stub =>
            Mark_Package_Body (Get_Body_From_Stub (N));

         when N_Package_Declaration =>
            Mark_Package_Declaration (N);

         when N_Parameter_Association =>
            Mark (Explicit_Actual_Parameter (N));

         when N_Pragma =>
            Mark_Pragma (N);

         when N_Procedure_Call_Statement =>
            Mark_Call (N);

         when N_Qualified_Expression =>
            Mark (Subtype_Mark (N));
            Mark (Expression (N));

         when N_Quantified_Expression =>
            if Present (Loop_Parameter_Specification (N)) then
               Mark (Discrete_Subtype_Definition
                      (Loop_Parameter_Specification (N)));
            else
               Mark (Iterator_Specification (N));
            end if;
            Mark (Condition (N));

         when N_Raise_Statement |
              N_Raise_xxx_Error =>

            --  A "raise statement" is only allowed when it is:
            --
            --    1. the only statement within an "if statement" that has no
            --       elsif/else parts.
            --
            --    2. the very last statement directly within a subprogram.

            if Present (Parent (N))
              and then Nkind (Parent (N)) = N_If_Statement
              and then Elsif_Parts (Parent (N)) = No_List
              and then Else_Statements (Parent (N)) = No_List
              and then List_Length (Then_Statements (Parent (N))) = 1
            then
               null;

            elsif Present (Parent (N))
              and then Nkind (Parent (N)) = N_Handled_Sequence_Of_Statements
              and then Present (Parent (Parent (N)))
              and then Nkind (Parent (Parent (N))) = N_Subprogram_Body
              and then Last (Statements
                               (Handled_Statement_Sequence
                                  (Parent (Parent (N))))) = N
            then
               null;

            --  The frontend inserts explicit checks during semantic analysis
            --  in some cases, for which gnatprove issues a corresponding
            --  check. Currently, this is only used for discriminant checks
            --  introduced when converting a discriminant type into another
            --  discriminant type, in which multiple source discriminants are
            --  mapped to the same target discriminant (RM 4.6(43)).

            elsif Nkind (N) in N_Raise_xxx_Error then
               case RT_Exception_Code'Val (UI_To_Int (Reason (N))) is
                  when CE_Discriminant_Check_Failed =>
                     null;
                  when others =>
                     Mark_Violation ("raise statement", N);
               end case;

            else
               Mark_Violation ("raise statement", N);
            end if;

         when N_Raise_Expression =>
            Mark_Violation ("raise expression", N);

         when N_Range =>
            Mark (Low_Bound (N));
            Mark (High_Bound (N));

         when N_Reference =>
            Mark_Violation ("reference", N);

         when N_Short_Circuit =>
            Mark_Actions (N, Actions (N));
            Mark (Left_Opnd (N));
            Mark (Right_Opnd (N));

         when N_Simple_Return_Statement =>
            Mark_Simple_Return_Statement (N);

         when N_Selected_Component =>

            --  In most cases, it is enough to look at the record type (the
            --  most underlying one) to see whether the access is in SPARK. An
            --  exception is the access to discrimants to a private type whose
            --  full view is not in SPARK.

            if not Is_Private_Type (Etype (Prefix (N)))
              or else In_SPARK (MUT (Etype (Prefix (N))))
            then
               Mark_Most_Underlying_Type_In_SPARK (Etype (Prefix (N)), N);
            elsif Ekind (Entity (Selector_Name (N))) /= E_Discriminant then
               Mark_Violation (N, From  => Etype (Prefix (N)));
            end if;

            Mark (Prefix (N));
            Mark (Selector_Name (N));

         when N_Slice =>
            Mark_Most_Underlying_Type_In_SPARK (Etype (Prefix (N)), N);
            Mark (Prefix (N));
            Mark (Discrete_Range (N));

         when N_Subprogram_Body =>

            --  For expression functions that have a unique declaration, the
            --  body inserted by the frontend may be far from the original
            --  point of declaration, after the private declarations of the
            --  package (to avoid premature freezing.) In those cases, mark the
            --  subprogram body at the same point as the subprogram
            --  declaration, so that entities declared afterwards have access
            --  to the axiom defining the expression function.

            if Present (Get_Expression_Function (Unique_Defining_Entity (N)))
              and then not Comes_From_Source (Original_Node (N))
            then
               null;
            else
               if Acts_As_Spec (N) then
                  Mark_Subprogram_Declaration (N);
               end if;
               Mark_Subprogram_Body (N);
            end if;

         when N_Subprogram_Body_Stub =>
            if Is_Subprogram_Stub_Without_Prior_Declaration (N) then
               Mark_Subprogram_Declaration (N);
            end if;
            Mark_Subprogram_Body (Get_Body_From_Stub (N));

         when N_Subprogram_Declaration =>
            Mark_Subprogram_Declaration (N);

            --  For expression functions that have a unique declaration, the
            --  body inserted by the frontend may be far from the original
            --  point of declaration, after the private declarations of the
            --  package (to avoid premature freezing.) In those cases, mark the
            --  subprogram body at the same point as the subprogram
            --  declaration, so that entities declared afterwards have access
            --  to the axiom defining the expression function.

            declare
               E      : constant Entity_Id := Defining_Entity (N);
               Body_N : constant Node_Id := SPARK_Util.Get_Subprogram_Body (E);
            begin
               if Present (Get_Expression_Function (E))
                 and then not Comes_From_Source (Original_Node (Body_N))
               then
                  Mark_Subprogram_Body (Body_N);
               end if;
            end;

         when N_Subtype_Indication =>
            Mark_Subtype_Indication (N);

         when N_Type_Conversion =>
            if Has_Array_Type (Etype (N)) then
               declare
                  Target_Comp_Typ : constant Entity_Id :=
                    MUT (Component_Type (MUT (Etype (N))));
                  Source_Comp_Typ : constant Entity_Id :=
                    MUT (Component_Type (MUT (Etype (Expression (N)))));
               begin
                  if Target_Comp_Typ /= Source_Comp_Typ then
                     Violation_Detected := True;
                     if SPARK_Pragma_Is (Opt.On) then
                        Error_Msg_N
                          ("conversion between array types that have "
                           & "different element types is not yet supported",
                           N);
                     end if;
                  end if;
               end;

            elsif Has_Fixed_Point_Type (Etype (N))
                    and then
                  Has_Fixed_Point_Type (Etype (Expression (N)))
            then
               declare
                  Target_Base_Type : constant Entity_Id :=
                    Base_Type (Etype (N));
                  Expr : constant Node_Id := Expression (N);

                  --  The multiplication and division operations on fixed-point
                  --  types have a return type of universal_fixed (with no
                  --  bounds), which is used as an overload resolution trick to
                  --  allow free conversion between certain real types on the
                  --  result of multiplication or division. Use the fixed-point
                  --  type of one of the operands as the source type for the
                  --  conversion.

                  Expr_Type : constant Entity_Id :=
                    (if Nkind_In (Expr, N_Op_Multiply, N_Op_Divide)
                       and then Etype (Expr) = Universal_Fixed
                     then
                       (if Has_Fixed_Point_Type (Etype (Left_Opnd (Expr))) then
                          Etype (Left_Opnd (Expr))
                        else
                          Etype (Right_Opnd (Expr)))
                     else
                        Etype (Expr));
                  Source_Base_Type : constant Entity_Id :=
                    Base_Type (Expr_Type);
               begin
                  if Target_Base_Type /= Source_Base_Type then
                     Violation_Detected := True;
                     if SPARK_Pragma_Is (Opt.On) then
                        Error_Msg_N
                          ("conversion between different fixed-point types "
                           & "is not yet supported", N);
                     end if;
                  end if;
               end;
            end if;

            Mark (Expression (N));

         when N_Unary_Op =>
            Mark_Unary_Op (N);

         when N_Unchecked_Type_Conversion =>
            Mark (Expression (N));

            --  Source unchecked type conversion nodes were rewritten as such
            --  by SPARK_Rewrite.Rewrite_Call, keeping the original call to an
            --  instance of Unchecked_Conversion as the Original_Node of the
            --  new N_Unchecked_Type_Conversion node, and marking the node as
            --  coming from source. We translate this original node to Why, so
            --  it should be in SPARK too.

            if Comes_From_Source (N) then
               Mark (Original_Node (N));
            end if;

         when N_Variant_Part =>
            declare
               Var : Node_Id := First (Variants (N));
            begin
               while Present (Var) loop
                  Mark (Var);
                  Next (Var);
               end loop;
            end;

         --  Frontend sometimes declares an Itype for the base type of a type
         --  declaration. This Itype should be marked at the point of
         --  declaration of the corresponding type, otherwise it may end up
         --  being marked multiple times in various client units, which leads
         --  to multiple definitions in Why3 for the same type.

         when N_Full_Type_Declaration         |
              N_Private_Extension_Declaration |
              N_Private_Type_Declaration      |
              N_Protected_Type_Declaration    |
              N_Subtype_Declaration           |
              N_Task_Type_Declaration         =>
            declare
               E  : constant Entity_Id := Defining_Entity (N);
               BT : constant Entity_Id := Base_Type (E);

            begin
               --  Store correspondance from completions of private types, so
               --  that Is_Full_View can be used for dealing correctly with
               --  private types, when the public part of the package is marked
               --  as SPARK_Mode On, and the private part of the package is
               --  marked as SPARK_Mode Off. This is also used later during
               --  generation of Why.

               if Ekind (E) in Private_Kind
                 and then Present (Full_View (E))
               then
                  Add_Full_And_Partial_View (Full_View (E), E);
               end if;

               Mark_Entity (E);
               if Is_Itype (BT) then
                  Mark_Entity (BT);
               end if;
            end;

         when N_Abort_Statement            |
              N_Accept_Statement           |
              N_Asynchronous_Select        |
              N_Conditional_Entry_Call     |
              N_Delay_Relative_Statement   |
              N_Delay_Until_Statement      |
              N_Entry_Body                 |
              N_Entry_Call_Statement       |
              N_Entry_Declaration          |
              N_Protected_Body             |
              N_Protected_Body_Stub        |
              N_Requeue_Statement          |
              N_Selective_Accept           |
              N_Single_Task_Declaration    |
              N_Task_Body                  |
              N_Task_Body_Stub             |
              N_Timed_Entry_Call           =>
            Mark_Violation ("tasking", N);

         --  The following kinds can be safely ignored by marking

         when N_At_Clause                              |
              N_Attribute_Definition_Clause            |
              N_Character_Literal                      |
              N_Enumeration_Representation_Clause      |
              N_Formal_Object_Declaration              |
              N_Formal_Package_Declaration             |
              N_Formal_Subprogram_Declaration          |
              N_Formal_Type_Declaration                |
              N_Freeze_Entity                          |
              N_Freeze_Generic_Entity                  |
              N_Function_Instantiation                 |
              N_Generic_Function_Renaming_Declaration  |
              N_Generic_Package_Declaration            |
              N_Generic_Package_Renaming_Declaration   |
              N_Generic_Procedure_Renaming_Declaration |
              N_Generic_Subprogram_Declaration         |
              N_Implicit_Label_Declaration             |
              N_Incomplete_Type_Declaration            |
              N_Itype_Reference                        |
              N_Label                                  |
              N_Null_Statement                         |
              N_Operator_Symbol                        |
              N_Others_Choice                          |
              N_Package_Instantiation                  |
              N_Package_Renaming_Declaration           |
              N_Procedure_Instantiation                |
              N_Record_Representation_Clause           |
              N_String_Literal                         |
              N_Subprogram_Renaming_Declaration        |
              N_Use_Package_Clause                     |
              N_With_Clause                            |
              N_Use_Type_Clause                        |
              N_Validate_Unchecked_Conversion          =>
            null;

         when N_Real_Literal |
           N_Integer_Literal =>

            --  If a literal is the result of the front-end
            --  rewriting a static attribute, then we mark
            --  the original node.
            if not Comes_From_Source (N) and then
              Is_Rewrite_Substitution (N) and then
              Nkind (Original_Node (N)) = N_Attribute_Reference
            then
               Mark_Attribute_Reference (Original_Node (N));
            end if;

         --  Object renamings are rewritten by expansion, but they are kept in
         --  the tree, so just ignore them.

         when N_Object_Renaming_Declaration =>
            null;

         --  The following nodes are rewritten by semantic analysis

         when N_Expression_Function =>
            raise Program_Error;

         --  The following nodes are never generated in GNATprove mode

         when N_Expression_With_Actions |
              N_Unchecked_Expression    =>
            raise Program_Error;

         --  Mark should not be called on other kinds

         when N_Abortable_Part |
              N_Accept_Alternative |
              N_Access_Definition |
              N_Access_Function_Definition |
              N_Access_Procedure_Definition |
              N_Access_To_Object_Definition |
              N_Aspect_Specification |
              N_Compilation_Unit |
              N_Compilation_Unit_Aux |
              N_Component_Clause |
              N_Component_Definition |
              N_Component_List |
              N_Constrained_Array_Definition  |
              N_Contract |
              N_Decimal_Fixed_Point_Definition |
              N_Defining_Character_Literal |
              N_Defining_Identifier |
              N_Defining_Operator_Symbol |
              N_Defining_Program_Unit_Name |
              N_Delay_Alternative |
              N_Delta_Constraint |
              N_Derived_Type_Definition |
              N_Designator |
              N_Digits_Constraint |
              N_Discriminant_Association |
              N_Discriminant_Specification |
              N_Function_Specification |
              N_Iteration_Scheme |
              N_Loop_Parameter_Specification |
              N_Elsif_Part |
              N_Empty |
              N_Entry_Body_Formal_Part |
              N_Enumeration_Type_Definition |
              N_Entry_Call_Alternative |
              N_Entry_Index_Specification |
              N_Error |
              N_Exception_Handler |
              N_Floating_Point_Definition |
              N_Formal_Decimal_Fixed_Point_Definition |
              N_Formal_Derived_Type_Definition |
              N_Formal_Discrete_Type_Definition |
              N_Formal_Floating_Point_Definition |
              N_Formal_Incomplete_Type_Definition |
              N_Formal_Modular_Type_Definition |
              N_Formal_Ordinary_Fixed_Point_Definition |
              N_Formal_Private_Type_Definition |
              N_Formal_Signed_Integer_Type_Definition |
              N_Generic_Association |
              N_Index_Or_Discriminant_Constraint |
              N_Mod_Clause |
              N_Modular_Type_Definition |
              N_Ordinary_Fixed_Point_Definition |
              N_Parameter_Specification |
              N_Pragma_Argument_Association |
              N_Package_Specification |
              N_Procedure_Specification |
              N_Protected_Definition |
              N_Push_Pop_xxx_Label |
              N_Range_Constraint |
              N_Real_Range_Specification |
              N_Record_Definition |
              N_SCIL_Dispatch_Table_Tag_Init |
              N_SCIL_Dispatching_Call |
              N_SCIL_Membership_Test |
              N_Signed_Integer_Type_Definition |
              N_Single_Protected_Declaration |
              N_Subunit |
              N_Task_Definition |
              N_Terminate_Alternative |
              N_Triggering_Alternative |
              N_Unconstrained_Array_Definition  |
              N_Unused_At_Start |
              N_Unused_At_End |
              N_Variant =>
            raise Program_Error;
      end case;
   end Mark;

   ------------------
   -- Mark_Actions --
   ------------------

   procedure Mark_Actions (N : Node_Id; L : List_Id) is
      function Acceptable_Actions (L : List_Id) return Boolean;
      --  Return whether L is a list of acceptable actions, which can be
      --  translated into Why.

      ------------------------
      -- Acceptable_Actions --
      ------------------------

      function Acceptable_Actions (L : List_Id) return Boolean is
         N : Node_Id;

      begin
         N := First (L);
         while Present (N) loop
            --  Only actions that consist in N_Object_Declaration nodes for
            --  constants are translated. All types are accepted and
            --  corresponding effects (for bounds of dynamic types) discarded
            --  when translating to Why.

            case Nkind (N) is
               when N_Subtype_Declaration   |
                    N_Full_Type_Declaration =>
                  null;

               when N_Object_Declaration =>
                  if Constant_Present (N) then
                     null;
                  else
                     return False;
                  end if;

               when N_Freeze_Entity =>
                  null;

               when others =>
                  return False;
            end case;

            Next (N);
         end loop;

         return True;
      end Acceptable_Actions;

      Save_Inside_Actions : constant Boolean := Inside_Actions;

   --  Start of Mark_Actions

   begin
      Inside_Actions := True;

      if Present (L) then
         Mark_List (L);
         if not Acceptable_Actions (L) then

            --  We should never reach here, but in case we do, we issue an
            --  understandable error message pointing to the source of the
            --  too complex actions.

            Error_Msg_N ("too complex actions inserted in expression", N);
         end if;
      end if;

      Inside_Actions := Save_Inside_Actions;
   end Mark_Actions;

   ------------------------------
   -- Mark_Attribute_Reference --
   ------------------------------

   procedure Mark_Attribute_Reference (N : Node_Id) is
      Aname   : constant Name_Id      := Attribute_Name (N);
      P       : constant Node_Id      := Prefix (N);
      Exprs   : constant List_Id      := Expressions (N);
      Attr_Id : constant Attribute_Id := Get_Attribute_Id (Aname);

   begin
      --  This case statement must agree with the table specified
      --  in SPARK RM 16.2 "Language Defined Attributes".
      --
      --  See also the analysis in Gnat2Why.Expr.Transform_Attr
      --  which defines which of these attributes are supported
      --  in proof.
      case Attr_Id is

         --  Support special aspects defined in SPARK
         when Attribute_Loop_Entry =>
            null;

         --  Support a subset of the aspects defined in Ada RM. These
         --  are the attributes marked "Yes" in RM 16.2
         when Attribute_Adjacent       |
           Attribute_Aft               |
           Attribute_Body_Version      |
           Attribute_Ceiling           |
           Attribute_Constrained       |
           Attribute_Copy_Sign         |
           Attribute_Definite          |
           Attribute_Delta             |
           Attribute_Denorm            |
           Attribute_Digits            |
           Attribute_First             |
           Attribute_First_Valid       |
           Attribute_Floor             |
           Attribute_Fore              |
           Attribute_Image             |
           Attribute_Last              |
           Attribute_Last_Valid        |
           Attribute_Length            |
           Attribute_Machine           |
           Attribute_Machine_Emax      |
           Attribute_Machine_Emin      |
           Attribute_Machine_Mantissa  |
           Attribute_Machine_Overflows |
           Attribute_Machine_Radix     |
           Attribute_Machine_Rounding  |
           Attribute_Machine_Rounds    |
           Attribute_Max               |
           Attribute_Min               |
           Attribute_Mod               |
           Attribute_Model             |
           Attribute_Model_Emin        |
           Attribute_Model_Epsilon     |
           Attribute_Model_Mantissa    |
           Attribute_Model_Small       |
           Attribute_Modulus           |
           Attribute_Old               |
           Attribute_Partition_ID      |
           Attribute_Pos               |
           Attribute_Pred              |
           Attribute_Range             |
           Attribute_Remainder         |
           Attribute_Result            |
           Attribute_Round             |
           Attribute_Rounding          |
           Attribute_Safe_First        |
           Attribute_Safe_Last         |
           Attribute_Scale             |
           Attribute_Scaling           |
           Attribute_Small             |
           Attribute_Succ              |
           Attribute_Truncation        |
           Attribute_Unbiased_Rounding |
           Attribute_Val               |
           Attribute_Value             |
           Attribute_Version           |
           Attribute_Wide_Image        |
           Attribute_Wide_Value        |
           Attribute_Wide_Width        |
           Attribute_Wide_Wide_Image   |
           Attribute_Wide_Wide_Value   |
           Attribute_Wide_Wide_Width   |
           Attribute_Width
         =>
            null;

         --  These attributes are supported, but generate a warning
         --  in "pedantic" mode, owing to their implemention-
         --  defined status. These are the attributes marked
         --  "Warn" in RM 16.2
         when Attribute_Address     |
           Attribute_Alignment      |
           Attribute_Bit_Order      |
           Attribute_Component_Size |
           Attribute_First_Bit      |
           Attribute_Last_Bit       |
           Attribute_Position       |
           Attribute_Size
         =>
            if Gnat2Why_Args.Pedantic then
               Error_Msg_Name_1 := Aname;
               Error_Msg_N
                 ("?attribute % has an implementation-defined value", N);
            end if;

         when Attribute_Update =>
            declare
               Pref_Typ : constant Entity_Id := Etype (P);
            begin
               if Is_Array_Type (Pref_Typ) then
                  if Number_Dimensions (Pref_Typ) > 1 then
                     Violation_Detected := True;
                     if SPARK_Pragma_Is (Opt.On) then
                        Error_Msg_N
                          ("attribute Update for multi-dimensional arrays is "
                             & "not yet supported",
                           N);
                     end if;
                     return;
                  end if;
               end if;
            end;

         when Attribute_Valid =>
            Error_Msg_F ("?attribute Valid is assumed to return True", N);

         when others =>
            Violation_Detected := True;
            if SPARK_Pragma_Is (Opt.On) then
               Error_Msg_Name_1 := Aname;
               Error_Msg_N ("attribute % is not permitted in SPARK", N);
            end if;
            return;
      end case;

      Mark (P);
      if Present (Exprs) then
         Mark_List (Exprs);
      end if;
   end Mark_Attribute_Reference;

   --------------------
   -- Mark_Binary_Op --
   --------------------

   procedure Mark_Binary_Op (N : Node_Id) is
   begin
      --  Only support for now multiplication and division operations on
      --  fixed-point types if both arguments and the result have the same
      --  base type, or one of the arguments is an integer type.

      if Nkind (N) in N_Op_Multiply | N_Op_Divide then
         declare
            L_Type : constant Entity_Id := Base_Type (Etype (Left_Opnd (N)));
            R_Type : constant Entity_Id := Base_Type (Etype (Right_Opnd (N)));

            --  The multiplication and division operations on fixed-point
            --  types have a return type of universal_fixed (with no
            --  bounds), which is used as an overload resolution trick to
            --  allow free conversion between certain real types on the
            --  result of multiplication or division. Use the fixed-point
            --  type of one of the operands as the source type for the
            --  conversion.

            Expr_Type : constant Entity_Id :=
              (if Etype (N) = Universal_Fixed then
                 Etype (Parent (N))
               else
                  Etype (N));
            E_Type : constant Entity_Id := Base_Type (Expr_Type);
         begin
            if Is_Fixed_Point_Type (L_Type)
                 and then
               Is_Fixed_Point_Type (R_Type)
                 and then
               L_Type /= R_Type
            then
               Violation_Detected := True;
               if SPARK_Pragma_Is (Opt.On) then
                  Error_Msg_N ("operation between different fixed-point types"
                               & " is not yet supported", N);
               end if;

            elsif (Is_Fixed_Point_Type (L_Type)
                     and then
                   Is_Floating_Point_Type (R_Type))
                     or else
                  (Is_Fixed_Point_Type (R_Type)
                     and then
                   Is_Floating_Point_Type (L_Type))
            then
               Violation_Detected := True;
               if SPARK_Pragma_Is (Opt.On) then
                  Error_Msg_N ("operation between fixed-point type and"
                               & " universal real is not yet supported", N);
               end if;

            elsif (Is_Fixed_Point_Type (L_Type) and then L_Type /= E_Type)
                     or else
                  (Is_Fixed_Point_Type (R_Type) and then R_Type /= E_Type)
            then
               Violation_Detected := True;
               if SPARK_Pragma_Is (Opt.On) then
                  Error_Msg_N ("operation on fixed-point type with different"
                               & " result type is not yet supported", N);
               end if;
            end if;
         end;
      end if;

      --  In pedantic mode, issue a warning whenever an arithmetic operation
      --  could be reordered by the compiler, like "A + B - C", as a given
      --  ordering may overflow and another may not. Not that a warning is
      --  issued even on operations like "A * B / C" which are not reordered
      --  by GNAT, as they could be reordered according to RM 4.5/13.

      if Gnat2Why_Args.Pedantic

        --  Ignore code defined in the standard library, unless the main unit
        --  is from the standard library. In particular, ignore code from
        --  instances of generics defined in the standard library (unless we
        --  are analyzing the standard library itself). As a result, no warning
        --  is generated in this case for standard library code. Such warnings
        --  are only noise, because a user sets the strict SPARK mode precisely
        --  when he uses another compiler than GNAT, with a different
        --  implementation of the standard library.

        and then
          (not Location_In_Standard_Library (Sloc (N))
            or else Unit_In_Standard_Library (Main_Unit))
      then
         case N_Binary_Op'(Nkind (N)) is
            when N_Op_Add | N_Op_Subtract =>
               if Nkind_In (Left_Opnd (N), N_Op_Add, N_Op_Subtract)
                 and then Paren_Count (Left_Opnd (N)) = 0
               then
                  Error_Msg_F
                    ("?possible reassociation due to missing parentheses",
                     Left_Opnd (N));
               end if;

               if Nkind_In (Right_Opnd (N), N_Op_Add, N_Op_Subtract)
                 and then Paren_Count (Right_Opnd (N)) = 0
               then
                  Error_Msg_F
                    ("?possible reassociation due to missing parentheses",
                     Right_Opnd (N));
               end if;

            when N_Op_Multiply | N_Op_Divide | N_Op_Mod | N_Op_Rem =>
               if Nkind (Left_Opnd (N)) in N_Multiplying_Operator
                 and then Paren_Count (Left_Opnd (N)) = 0
               then
                  Error_Msg_F
                    ("?possible reassociation due to missing parentheses",
                     Left_Opnd (N));
               end if;

               if Nkind (Right_Opnd (N)) in N_Multiplying_Operator
                 and then Paren_Count (Right_Opnd (N)) = 0
               then
                  Error_Msg_F
                    ("?possible reassociation due to missing parentheses",
                     Right_Opnd (N));
               end if;

            when others =>
               null;
         end case;
      end if;

      Mark (Left_Opnd (N));
      Mark (Right_Opnd (N));
   end Mark_Binary_Op;

   ---------------
   -- Mark_Call --
   ---------------

   procedure Mark_Call (N : Node_Id) is
      Nam     : constant Node_Id := Name (N);
      E       : Node_Id;
      Actuals : constant List_Id := Parameter_Associations (N);

   begin

      if Present (Actuals) then
         Mark_List (Actuals);
      end if;

      --  If this is an indirect call or the subprogram called is not in SPARK,
      --  then the call is not in SPARK.

      if not Is_Entity_Name (Nam)
        or else No (Entity (Nam))
      then
         if Nkind (Nam) = N_Explicit_Dereference then
            if Nkind (N) = N_Procedure_Call_Statement then
               Mark_Violation ("call through access to procedure", N);
            else
               pragma Assert (Nkind (N) = N_Function_Call);
               Mark_Violation ("call through access to function", N);
            end if;

         else
            --  Are there cases where we reach here??? For the moment, issue a
            --  generic error message about "indirect calls".

            Mark_Violation ("indirect call", N);
         end if;

      --  ??? Ignore calls to predicate functions (MC20-028)

      elsif not In_SPARK (Entity (Nam))
        and then not Is_Predicate_Function (Entity (Nam))
      then
         Mark_Violation (N, From => Entity (Nam));

      else
         E := Entity (Nam);

         --  Issue a warning for calls to subprograms with no Global contract,
         --  either manually-written or computed. This is the case for standard
         --  and external library subprograms for which no Global contract
         --  is supplied. Note that subprograms for which an external
         --  axiomatization is provided are exempted, as they should not
         --  have any effect on global items.
         --  Exempt also pure subprograms which have no global effects.

         if not Has_Computed_Global (E)
           and then No (Get_Pragma (E, Pragma_Global))
           and then not Entity_In_External_Axioms (E)
           and then not Is_Pure (E)
         then
            Error_Msg_NE
              ("?no Global contract available for &", N, E);
            Error_Msg_NE
              ("\\assuming & has no effect on global items", N, E);
         end if;
      end if;
   end Mark_Call;

   ---------------------------
   -- Mark_Compilation_Unit --
   ---------------------------

   procedure Mark_Compilation_Unit (N : Node_Id) is
      CU        : constant Node_Id := Parent (N);
      Context_N : Node_Id;

   begin
      Initialize;

      --  Separately mark declarations from Standard as in SPARK or not

      if Defining_Entity (N) = Standard_Standard then
         return;
      end if;

      --  Mark entities in SPARK or not

      Context_N := First (Context_Items (CU));
      while Present (Context_N) loop
         Mark (Context_N);
         Next (Context_N);
      end loop;

      Mark (N);
   end Mark_Compilation_Unit;

   --------------------------------
   -- Mark_Component_Declaration --
   --------------------------------

   procedure Mark_Component_Declaration (N : Node_Id) is
      Def : constant Node_Id   := Component_Definition (N);

   begin
      if Aliased_Present (Def) then
         Mark_Violation ("ALIASED", N);
      end if;

      if Present (Access_Definition (Def)) then
         Mark_Violation ("access type", Def);
      else
         Mark_Subtype_Indication (Subtype_Indication (Def));
      end if;
   end Mark_Component_Declaration;

   -----------------------------
   -- Mark_Handled_Statements --
   -----------------------------

   procedure Mark_Handled_Statements (N : Node_Id) is
      Handlers : constant List_Id := Exception_Handlers (N);

   begin
      if Present (Handlers) then
         Mark_Violation ("handler", First (Handlers));
      end if;

      Mark_List (Statements (N));
   end Mark_Handled_Statements;

   --------------------------------------
   -- Mark_Identifier_Or_Expanded_Name --
   --------------------------------------

   procedure Mark_Identifier_Or_Expanded_Name (N : Node_Id) is
      E : Entity_Id;
   begin
      if Is_Entity_Name (N) and then Present (Entity (N)) then
         E := Entity (N);

         case Ekind (E) is
            when Object_Kind =>
               if (Ekind_In (E, E_Variable, E_Constant)
                    or else Ekind (E) in Formal_Kind)
                 and then not In_SPARK (Entity (N))
               then
                  Mark_Violation (N, From => Entity (N));
               end if;

            when Named_Kind =>
               if not In_SPARK (Entity (N)) then
                  Mark_Violation (N, From => Entity (N));
               end if;

            when Type_Kind =>
               if not In_SPARK (Entity (N)) then
                  Mark_Violation (N, From => Entity (N));
               end if;

            --  Subprogram name appears for example in Sub'Result

            when E_Void                  |
                 E_Enumeration_Literal   |
                 Subprogram_Kind         |
                 E_Block                 |
                 Generic_Subprogram_Kind |
                 E_Generic_Package       |
                 E_Label                 |
                 E_Loop                  |
                 E_Return_Statement      |
                 E_Package               |
                 E_Package_Body          |
                 E_Subprogram_Body       =>
               null;

            --  Abstract state entities are passed directly to Mark_Entity

            when E_Abstract_State =>
               raise Program_Error;

            when E_Exception =>
               Mark_Violation ("exception", N);

            when E_Entry                 |
                 E_Entry_Family          |
                 E_Entry_Index_Parameter |
                 E_Protected_Object      |
                 E_Protected_Body        |
                 E_Task_Body             =>
               Mark_Violation ("tasking", N);
         end case;
      end if;
   end Mark_Identifier_Or_Expanded_Name;

   ------------------------
   -- Mark_If_Expression --
   ------------------------

   procedure Mark_If_Expression (N : Node_Id) is
      Condition : constant Node_Id := First (Expressions (N));
      Then_Expr : constant Node_Id := Next (Condition);
      Else_Expr : Node_Id;

   begin
      Mark_Actions (N, Then_Actions (N));
      Mark_Actions (N, Else_Actions (N));

      Else_Expr := Next (Then_Expr);

      Mark (Condition);
      Mark (Then_Expr);

      if Present (Else_Expr) then
         Mark (Else_Expr);
      end if;
   end Mark_If_Expression;

   -----------------------
   -- Mark_If_Statement --
   -----------------------

   procedure Mark_If_Statement (N : Node_Id) is
   begin
      Mark (Condition (N));

      Mark_List (Then_Statements (N));

      if Present (Elsif_Parts (N)) then
         declare
            Part : Node_Id;

         begin
            Part := First (Elsif_Parts (N));
            while Present (Part) loop
               Mark_Actions (N, Condition_Actions (Part));
               Mark (Condition (Part));
               Mark_List (Then_Statements (Part));
               Next (Part);
            end loop;
         end;
      end if;

      if Present (Else_Statements (N)) then
         Mark_List (Else_Statements (N));
      end if;
   end Mark_If_Statement;

   ---------------------------
   -- Mark_Iteration_Scheme --
   ---------------------------

   procedure Mark_Iteration_Scheme (N : Node_Id) is
   begin
      if Present (Condition (N)) then
         Mark_Actions (N, Condition_Actions (N));
         Mark (Condition (N));

      elsif Present (Loop_Parameter_Specification (N)) then
         pragma Assert (No (Condition_Actions (N)));
         Mark (Discrete_Subtype_Definition
               (Loop_Parameter_Specification (N)));

         --  The loop parameter shall be added to the entities in SPARK
         declare
            Loop_Index : constant Entity_Id :=
              Defining_Identifier (Loop_Parameter_Specification (N));
         begin
            Mark_Entity (Loop_Index);
         end;

      else
         pragma Assert (No (Condition_Actions (N)));
         pragma Assert (Present (Iterator_Specification (N)));
         Mark_Violation ("loop with iterator", N);
      end if;
   end Mark_Iteration_Scheme;

   ---------------
   -- Mark_List --
   ---------------

   procedure Mark_List (L : List_Id) is
      N : Node_Id;
   begin
      N := First (L);
      while Present (N) loop
         Mark (N);
         Next (N);
      end loop;
   end Mark_List;

   -----------------------------
   -- Mark_Number_Declaration --
   -----------------------------

   procedure Mark_Number_Declaration (N : Node_Id) is
      E : constant Entity_Id := Defining_Entity (N);
   begin
      Mark_Entity (E);
   end Mark_Number_Declaration;

   -----------------------------
   -- Mark_Object_Declaration --
   -----------------------------

   procedure Mark_Object_Declaration (N : Node_Id) is
      E : constant Entity_Id := Defining_Entity (N);

   begin
      --  Mark entity
      Mark_Entity (E);
   end Mark_Object_Declaration;

   -----------------------
   -- Mark_Package_Body --
   -----------------------

   procedure Mark_Package_Body (N : Node_Id) is
      Save_SPARK_Pragma : constant Node_Id := Current_SPARK_Pragma;
      Id  : constant Entity_Id := Unique_Defining_Entity (N);
      HSS : constant Node_Id := Handled_Statement_Sequence (N);

   begin
      --  Do not analyze generic bodies

      if Ekind (Id) = E_Generic_Package then
         return;
      end if;

      --  Do not analyze bodies for packages with external axioms

      if Entity_In_External_Axioms (Id) then
         return;
      end if;

      Current_SPARK_Pragma := SPARK_Pragma (Defining_Entity (N));

      Mark_List (Declarations (N));

      Current_SPARK_Pragma := SPARK_Aux_Pragma (Defining_Entity (N));

      --  Only analyze package body statements in SPARK_Mode => On

      if SPARK_Pragma_Is (Opt.On) then

         --  Always mark the body in SPARK

         Bodies_In_SPARK.Include (Id);

         if Present (HSS) then
            Mark (HSS);
         end if;
      end if;

      --  Postprocessing: indicate in output file if package is in
      --  SPARK or not, for reporting, debug and verifications.

      Generate_Output_In_Out_SPARK (Id);

      Current_SPARK_Pragma := Save_SPARK_Pragma;
   end Mark_Package_Body;

   ------------------------------
   -- Mark_Package_Declaration --
   ------------------------------

   procedure Mark_Package_Declaration (N : Node_Id) is
      Save_SPARK_Pragma : constant Node_Id := Current_SPARK_Pragma;
      Id         : constant Entity_Id := Defining_Entity (N);
      Vis_Decls  : constant List_Id :=
                     Visible_Declarations (Specification (N));
      Priv_Decls : constant List_Id :=
                     Private_Declarations (Specification (N));

   begin
      --  Mark package in SPARK if fully in SPARK_Mode => On (including the
      --  private part), or if the visible part is in SPARK_Mode => On and
      --  it has external axiomatization.

      Current_SPARK_Pragma := SPARK_Aux_Pragma (Id);

      if SPARK_Pragma_Is (Opt.On) then
         Mark_Entity (Id);

      else
         Current_SPARK_Pragma := SPARK_Pragma (Id);

         if Entity_In_External_Axioms (Id) then
            Mark_Entity (Id);
         end if;
      end if;

      --  Nothing more to do for packages with external axiomatization

      if Entity_In_External_Axioms (Id) then
         return;
      end if;

      Current_SPARK_Pragma := SPARK_Pragma (Id);

      --  Mark abstract state entities

      declare
         States : constant Elist_Id := Abstract_States (Id);
         State  : Elmt_Id;
      begin
         if Present (States) then
            State := First_Elmt (States);
            while Present (State)
              and then not Is_Null_State (Node (State))
            loop
               Mark_Entity (Node (State));
               Next_Elmt (State);
            end loop;
         end if;
      end;

      if SPARK_Pragma_Is (Opt.On) then
         Specs_In_SPARK.Include (Id);
      end if;

      if Present (Vis_Decls) then
         Mark_List (Vis_Decls);
      end if;

      Current_SPARK_Pragma := SPARK_Aux_Pragma (Id);

      if Present (Priv_Decls) then
         Mark_List (Priv_Decls);
      end if;

      Current_SPARK_Pragma := Save_SPARK_Pragma;

      --  Postprocessing: indicate in output file if package is in SPARK or
      --  not, for reporting, debug and verifications. Only do so if there
      --  is no corresponding package body, otherwise it is reported when
      --  marking the package body.

      if Is_In_Current_Unit (Id) and then No (Get_Package_Body (Id)) then
         Generate_Output_In_Out_SPARK (Id);
      end if;
   end Mark_Package_Declaration;

   -----------------
   -- Mark_Pragma --
   -----------------

   --  gnatprove currently deals with a subset of the Ada and GNAT pragmas.
   --  Other recognized pragmas are ignored, and a warning is issued here (and
   --  in flow analysis, and in proof) that the pragma is ignored. Any change
   --  in the set of pragmas that gnatprove supports should be reflected:
   --    . in Mark_Pragma below
   --    . for flow analysis, in Pragma_Relevant_To_Flow in
   --      flow-control_flow_graph.adb
   --    . for proof, in Transform_Pragma in gnat2why-expr.adb

   procedure Mark_Pragma (N : Node_Id) is
      Pname   : constant Name_Id   := Pragma_Name (N);
      Prag_Id : constant Pragma_Id := Get_Pragma_Id (Pname);

      Arg1 : Node_Id;
      Arg2 : Node_Id;
      --  First two pragma arguments (pragma argument association nodes, or
      --  Empty if the corresponding argument does not exist).

   begin
      if Present (Pragma_Argument_Associations (N)) then
         Arg1 := First (Pragma_Argument_Associations (N));

         if Present (Arg1) then
            Arg2 := Next (Arg1);
         end if;
      end if;

      case Prag_Id is

         --  pragma Check ([Name    =>] Identifier,
         --                [Check   =>] Boolean_Expression
         --              [,[Message =>] String_Expression]);

         when Pragma_Check =>

            --  Ignore pragma Check for preconditions and postconditions

            if Is_Pragma_Check (N, Name_Precondition)
                 or else
               Is_Pragma_Check (N, Name_Pre)
                 or else
               Is_Pragma_Check (N, Name_Postcondition)
                 or else
               Is_Pragma_Check (N, Name_Post)
            then
               null;
            else
               Mark (Get_Pragma_Arg (Arg2));
            end if;

         --  pragma Loop_Variant
         --         ( LOOP_VARIANT_ITEM {, LOOP_VARIANT_ITEM } );

         --  LOOP_VARIANT_ITEM ::= CHANGE_DIRECTION => discrete_EXPRESSION

         --  CHANGE_DIRECTION ::= Increases | Decreases

         when Pragma_Loop_Variant =>
            declare
               Variant : Node_Id;
            begin
               --  Process all increasing / decreasing expressions

               Variant := First (Pragma_Argument_Associations (N));
               while Present (Variant) loop
                  Mark (Expression (Variant));
                  Next (Variant);
               end loop;
            end;

         when Pragma_Import =>
            --  If the associated node of Pragma_Import:
            --     1. is a subprogram
            --     2. and is marked as In-SPARK
            --     3. and no global aspect has been specified
            --     4. and the subprogram is not Pure
            --  then we warn that null global effect was assumed.
            declare
               Argument_Associations : constant List_Id :=
                 Pragma_Argument_Associations (N);

               Associated_Subprogram : constant Node_Id :=
                 Associated_Node (Expression
                                    (Next (First (Argument_Associations))));
            begin
               if Ekind (Associated_Subprogram) in Subprogram_Kind
                 and then Entity_In_SPARK (Associated_Subprogram)
                 and then No (Get_Pragma
                                (Associated_Subprogram, Pragma_Global))
                 and then not Is_Pure (Associated_Subprogram)
               then
                  Error_Msg_N ("?null global effect assumed on imported"
                                 & " subprogram", Associated_Subprogram);
               end if;
            end;

         when Pragma_Overflow_Mode =>
            Error_Msg_F ("?pragma Overflow_Mode in code is ignored", N);

         --  Pragmas that do not need any marking, either because:
         --  . they are defined by SPARK 2014, or
         --  . they are already taken into account elsewhere (contracts)
         --  . they have no effect on verification

         --  Group 1 - RM Table 17.1(1), pragmas marked "Yes"
         --  Note: pragma Assert is transformed into an
         --  instance of pragma Check by the front-end.
         when Pragma_Assertion_Policy             |
              Pragma_Atomic                       |
              Pragma_Atomic_Components            |
              Pragma_Convention                   |
              Pragma_Elaborate                    |
              Pragma_Elaborate_All                |
              Pragma_Elaborate_Body               |
              Pragma_Export                       |
              Pragma_Independent                  |
              Pragma_Independent_Components       |
              Pragma_Inline                       |
              Pragma_Inspection_Point             |
              Pragma_Linker_Options               |
              Pragma_List                         |
              Pragma_No_Return                    |
              Pragma_Normalize_Scalars            |
              Pragma_Optimize                     |
              Pragma_Pack                         |
              Pragma_Page                         |
              Pragma_Partition_Elaboration_Policy |
              Pragma_Preelaborable_Initialization |
              Pragma_Preelaborate                 |
              Pragma_Profile                      |
              Pragma_Pure                         |
              Pragma_Restrictions                 |
              Pragma_Reviewable                   |
              Pragma_Suppress                     |
              Pragma_Unsuppress                   |
              Pragma_Volatile                     |

         --  Group 2 - RM Table 17.1(2), pragmas marked "Yes"
         --  Note: pragmas Assert_And_Cut, Assume, and
         --  Loop_Invariant are transformed into instances of
         --  pragma Check by the front-end.
              Pragma_Abstract_State               |
              Pragma_Assume_No_Invalid_Values     |
              Pragma_Async_Readers                |
              Pragma_Async_Writers                |
              Pragma_Contract_Cases               |
              Pragma_Depends                      |
              Pragma_Effective_Reads              |
              Pragma_Effective_Writes             |
              Pragma_Global                       |
              Pragma_Initializes                  |
              Pragma_Initial_Condition            |
              Pragma_Part_Of                      |
              Pragma_Postcondition                |
              Pragma_Precondition                 |
              Pragma_Refined_Depends              |
              Pragma_Refined_Global               |
              Pragma_Refined_Post                 |
              Pragma_Refined_State                |
              Pragma_SPARK_Mode                   |

         --  Group 3 - RM Table 17.1(3), pragmas marked "Yes"
         --  Note: pragma Debug is removed by the front-end.
              Pragma_Ada_83                       |
              Pragma_Ada_95                       |
              Pragma_Ada_05                       |
              Pragma_Ada_2005                     |
              Pragma_Ada_12                       |
              Pragma_Ada_2012                     |
              Pragma_Annotate                     |
              Pragma_Check_Policy                 |
              Pragma_Inline_Always                |
              Pragma_Pure_Function                |
              Pragma_Restriction_Warnings         |
              Pragma_Style_Checks                 |
              Pragma_Test_Case                    |
              Pragma_Unmodified                   |
              Pragma_Unreferenced                 |
              Pragma_Validity_Checks              |
              Pragma_Warnings                     =>
            null;

         when Unknown_Pragma =>
            Error_Msg_Name_1 := Pname;
            Mark_Violation ("unknown pragma %", N);

         when others =>
            Error_Msg_Name_1 := Pname;
            Error_Msg_N ("?pragma % is not yet supported", N);
            Error_Msg_N ("\\it is currently ignored", N);
      end case;
   end Mark_Pragma;

   ----------------------------------
   -- Mark_Simple_Return_Statement --
   ----------------------------------

   procedure Mark_Simple_Return_Statement (N : Node_Id) is
   begin
      if Present (Expression (N)) then
         Mark (Expression (N));
      end if;
   end Mark_Simple_Return_Statement;

   ------------------------------------
   -- Mark_Extended_Return_Statement --
   ------------------------------------

   procedure Mark_Extended_Return_Statement (N : Node_Id) is
   begin
      Mark_List (Return_Object_Declarations (N));

      if Present (Handled_Statement_Sequence (N)) then
         Mark (Handled_Statement_Sequence (N));
      end if;
   end Mark_Extended_Return_Statement;

   ---------------------------
   -- Mark_Standard_Package --
   ---------------------------

   procedure Mark_Standard_Package is

      procedure Insert_All_And_SPARK (E : Entity_Id);

      --------------------------
      -- Insert_All_And_SPARK --
      --------------------------

      procedure Insert_All_And_SPARK (E : Entity_Id) is
      begin
         Entity_Set.Insert (E);
         Entities_In_SPARK.Insert (E);
      end Insert_All_And_SPARK;

      --  Standard types which are in SPARK are associated to True

      Standard_Type_Is_In_SPARK : constant array (S_Types) of Boolean :=
        (S_Boolean             => True,

         S_Short_Short_Integer => True,
         S_Short_Integer       => True,
         S_Integer             => True,
         S_Long_Integer        => True,
         S_Long_Long_Integer   => True,

         S_Natural             => True,
         S_Positive            => True,

         S_Short_Float         => True,
         S_Float               => True,
         S_Long_Float          => True,
         S_Long_Long_Float     => True,

         S_Character           => True,
         S_Wide_Character      => True,
         S_Wide_Wide_Character => True,

         S_String              => True,
         S_Wide_String         => True,
         S_Wide_Wide_String    => True,

         S_Duration            => True);

   begin
      Initialize;

      for S in S_Types loop
         Entity_Set.Insert (Standard_Entity (S));
         Entity_Set.Include (Etype (Standard_Entity (S)));
         if Standard_Type_Is_In_SPARK (S) then
            Entities_In_SPARK.Insert (Standard_Entity (S));
            Entities_In_SPARK.Include (Etype (Standard_Entity (S)));
         end if;
      end loop;

      for S in S_ASCII_Names loop
         Insert_All_And_SPARK (Standard_Entity (S));
      end loop;

      Insert_All_And_SPARK (Standard_Void_Type);

      Insert_All_And_SPARK (Standard_False);
      Insert_All_And_SPARK (Standard_True);

      Insert_All_And_SPARK (Universal_Integer);
      Insert_All_And_SPARK (Universal_Real);
      Insert_All_And_SPARK (Universal_Fixed);

      Insert_All_And_SPARK (Standard_Integer_8);
      Insert_All_And_SPARK (Standard_Integer_16);
      Insert_All_And_SPARK (Standard_Integer_32);
      Insert_All_And_SPARK (Standard_Integer_64);
   end Mark_Standard_Package;

   --------------------------
   -- Mark_Subprogram_Body --
   --------------------------

   procedure Mark_Subprogram_Body (N : Node_Id) is
      Save_SPARK_Pragma : constant Node_Id := Current_SPARK_Pragma;
      E   : constant Entity_Id := Unique_Defining_Entity (N);
      HSS : constant Node_Id   := Handled_Statement_Sequence (N);

   begin
      --  Ignore bodies defined in the standard library, unless the main unit
      --  is from the standard library. In particular, ignore bodies from
      --  instances of generics defined in the standard library (unless we
      --  are analyzing the standard library itself). As a result, no VC is
      --  generated in this case for standard library code.

      if Location_In_Standard_Library (Sloc (N))
        and not Unit_In_Standard_Library (Main_Unit)
      then
         return;
      end if;

      --  Content of packages with external axioms is not to be proved

      if Entity_In_External_Axioms (E) then
         return;
      end if;

      --  Do not analyze generic bodies

      if Ekind (E) in Generic_Subprogram_Kind then
         return;
      end if;

      Current_SPARK_Pragma := SPARK_Pragma (Defining_Entity (N));

      --  Only analyze subprogram body declarations in SPARK_Mode => On

      if SPARK_Pragma_Is (Opt.On) then

         --  Always mark the body in SPARK

         Bodies_In_SPARK.Include (E);

         --  Detect violations in the body itself

         Mark_List (Declarations (N));
         Mark (HSS);

         --  For the special case of an expression function, the frontend
         --  generates a distinct body if not already in source code. Use as
         --  entity for the body the distinct E_Subprogram_Body entity. This
         --  allows a separate definition of theories in Why3 for declaring
         --  the logic function and its axiom. This is necessary so that they
         --  are defined with the proper visibility over previously defined
         --  entities.

         if Ekind (E) = E_Function
           and then Present (Get_Expression_Function (E))
         then
            Entity_List.Append (Defining_Entity (N));
         end if;
      end if;

      --  Postprocessing: indicate in output file if subprogram is in
      --  SPARK or not, for reporting, debug and verifications.

      Generate_Output_In_Out_SPARK (E);

      Current_SPARK_Pragma := Save_SPARK_Pragma;
   end Mark_Subprogram_Body;

   ---------------------------------
   -- Mark_Subprogram_Declaration --
   ---------------------------------

   procedure Mark_Subprogram_Declaration (N : Node_Id) is
      Save_SPARK_Pragma : constant Node_Id := Current_SPARK_Pragma;
      E : constant Entity_Id := Defining_Entity (N);

   begin
      --  Do not analyze generics

      if Ekind (E) in Generic_Subprogram_Kind then
         return;
      end if;

      --  Mark entity

      Current_SPARK_Pragma := SPARK_Pragma (E);

      if SPARK_Pragma_Is (Opt.On) then
         Specs_In_SPARK.Include (E);
      end if;

      Mark_Entity (E);

      Current_SPARK_Pragma := Save_SPARK_Pragma;
   end Mark_Subprogram_Declaration;

   -----------------------------
   -- Mark_Subtype_Indication --
   -----------------------------

   procedure Mark_Subtype_Indication (N : Node_Id) is
      T       : Entity_Id;
      Cstr    : Node_Id;

   begin
      if Nkind (N) = N_Subtype_Indication then
         T := Etype (Subtype_Mark (N));
      else
         T := Etype (N);
      end if;

      --  Check that the base type is in SPARK

      if not In_SPARK (T) then
         Mark_Violation (N, From => T);
      end if;

      if Nkind (N) = N_Subtype_Indication then

         Cstr := Constraint (N);
         case Nkind (Cstr) is
            when N_Range_Constraint =>
               null;

            when N_Index_Or_Discriminant_Constraint =>

               if Is_Array_Type (T) then
                  Cstr := First (Constraints (Cstr));
                  while Present (Cstr) loop

                     case Nkind (Cstr) is
                     when N_Identifier | N_Expanded_Name =>
                        if not In_SPARK (Entity (Cstr)) then
                           Mark_Violation (N, From => Entity (Cstr));
                        end if;

                     when N_Subtype_Indication =>
                        if not In_SPARK (Subtype_Mark (Cstr)) then
                           Mark_Violation (N, From => Subtype_Mark (Cstr));
                        end if;

                     when N_Range =>
                        null;

                     when others =>
                        raise Program_Error;
                     end case;
                     Next (Cstr);
                  end loop;

               --  Note that a discriminant association that has no selector
               --  name list appears directly as an expression in the tree.

               else
                  null;
               end if;

            when N_Digits_Constraint =>
               null;

            when N_Delta_Constraint =>
               null;

            when others =>  --  TO DO ???
               raise Program_Error;
         end case;
      end if;
   end Mark_Subtype_Indication;

   -------------------
   -- Mark_Unary_Op --
   -------------------

   procedure Mark_Unary_Op (N : Node_Id) is
   begin
      Mark (Right_Opnd (N));
   end Mark_Unary_Op;

   ----------------------------------
   -- Most_Underlying_Type_In_SPARK --
   ----------------------------------

   procedure Mark_Most_Underlying_Type_In_SPARK (Id : Entity_Id; N : Node_Id)
   is
      Typ : constant Entity_Id := MUT (Id);
   begin
      if not In_SPARK (Typ) then
         Mark_Violation (N, From => Typ);
      end if;
   end Mark_Most_Underlying_Type_In_SPARK;

end SPARK_Definition;
