------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      S P A R K _ D E F I N I T I O N                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                      Copyright (C) 2011-2013, AdaCore                    --
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

with Ada.Strings.Unbounded;              use Ada.Strings.Unbounded;
with Ada.Text_IO;                        use Ada.Text_IO;
with Ada.Strings.Fixed;
with Ada.Strings.Maps.Constants;
with Ada.Containers.Doubly_Linked_Lists; use Ada.Containers;
with Ada.Containers.Hashed_Maps;

with AA_Util;                            use AA_Util;
with Atree;                              use Atree;
with Einfo;                              use Einfo;
with Errout;                             use Errout;
with Lib;
with Namet;                              use Namet;
with Nlists;                             use Nlists;
with Opt;
with Sem_Prag;
with Sem_Util;                           use Sem_Util;
with Sinfo;                              use Sinfo;
with Sinput;                             use Sinput;
with Snames;                             use Snames;
with Stand;                              use Stand;

with SPARK_Frame_Conditions;             use SPARK_Frame_Conditions;
with SPARK_Util;                         use SPARK_Util;
with SPARK_Violations;                   use all type SPARK_Violations.Vkind;

package body SPARK_Definition is

   -----------------------------------
   -- Handling of SPARK_Mode Pragma --
   -----------------------------------

   --  Prior to marking, the tree is traversed to compute scope information:
   --  . attach the applicable SPARK_Mode pragma to each entity, if any
   --  . compute the correspondance between full and partial views, for private
   --    types and deferred constants

   --  The SPARK_Mode pragma may be used as a configuration pragma or a local
   --  pragma in the source. The frontend rejects all invalid placements of
   --  this pragma, and stores them in the attribute "SPARK_Mode_Pragmas" of
   --  the relevant entities:

   --      E_Function
   --      E_Generic_Function
   --      E_Generic_Procedure
   --      E_Procedure
   --      E_Subprogram_Body
   --      E_Generic_Package
   --      E_Package
   --      E_Package_Body

   --  [Generic] package specs and bodies may have two pragmas. Those are
   --  linked using the Next_Pragma field. To distinguish between pragmas that
   --  apply to the visible or private part of a spec, one can use function
   --
   --      sem_prag.Is_Private_SPARK_Mode
   --
   --  To distinguish between pragmas that apply to the declarative and
   --  statement part of a body, one can use function
   --
   --      sem_prag.Is_Elaboration_SPARK_Mode
   --
   --  The unit-wide configuration version of the pragma is associated
   --  with the unit itself. See the facilities in lib.ads and function
   --  SPARK_Mode_Pragma.
   --
   --  The compilation-wide configuration mode of the pragma is retained in
   --  opt.ads. See opt.ads.
   --
   --  There is a special type called SPARK_Mode_Id which defines the various
   --  modes. There is a useful function in sem_prag to extract the Mode_Id
   --  from a pragma
   --
   --      sem_prag.Get_SPARK_Mode_Id
   --
   --  The idea is that one should compare SPARK_Mode_Id values rather than
   --  Name_Ids.

   package Applicable_SPARK_Mode is new
     Hashed_Maps (Key_Type     => Entity_Id,
                  Hash         => Node_Hash,
                  Element_Type => Node_Id,
                  Equivalent_Keys => "=",
                  "="             => "=");
   --  Mapping from entities to the applicable SPARK_Mode pragma, if any

   Applicable_SPARK_Mode_For_Spec : Applicable_SPARK_Mode.Map;
   Applicable_SPARK_Mode_For_Body : Applicable_SPARK_Mode.Map;
   --  SPARK_Mode pragma applicable to the "spec" and "body" views of an
   --  entity, if any.

   function Get_Applicable_SPARK_Pragma
     (E       : Entity_Id;
      Is_Body : Boolean := False) return Node_Id
   with Pre => Ekind (E) /= E_Subprogram_Body;
   --  Returns the applicable SPARK_Mode pragma for entity E, if any. If
   --  Is_Body is False, this applies to the spec view of entity E. If Is_Body
   --  is True, this applies to the body view of entity E. E needs not be a
   --  unique entity. This does not apply currently to the global SPARK_Mode
   --  pragma, which is not directly available (only its presence and value
   --  is known).

   function Applicable_SPARK_Pragma_Is
     (E       : Entity_Id;
      Mode    : SPARK_Mode_Id;
      Is_Body : Boolean := False) return Boolean;
   --  Returns True if the applicable SPARK_Pragma for entity E has value Mode,
   --  whether it comes from a local or a global SPARK_Mode pragma.

   package SPARK_Mode_Stack is new
     Doubly_Linked_Lists (Element_Type => Node_Id,
                          "="          => "=");
   --  Stack of SPARK_Mode pragmas for the currently opened scopes. If the list
   --  is not empty, its first element is the currently applicable pragma.

   SPARK_Mode_Pragmas_Stack : SPARK_Mode_Stack.List;
   --  The global stack of SPARK_Mode pragmas

   procedure Get_Scope_Info (N : Node_Id);
   --  Initial recursive traversal of the AST to store for each entity or node
   --  the relevant scope information:
   --  . for each entity, the applicable SPARK_Mode pragma, if any
   --  . for each node, the applicable Overflow_Mode pragma, if any (not done
   --    yet)

   --------------------------------
   -- Applicable_SPARK_Pragma_Is --
   --------------------------------

   function Applicable_SPARK_Pragma_Is
     (E       : Entity_Id;
      Mode    : SPARK_Mode_Id;
      Is_Body : Boolean := False) return Boolean
   is
      Prag : constant Node_Id := Get_Applicable_SPARK_Pragma (E, Is_Body);

   begin
      if Present (Prag) then
         return Sem_Prag.Get_SPARK_Mode_Id (Prag) = Mode;
      else
         return Opt.Global_SPARK_Mode = Mode;
      end if;
   end Applicable_SPARK_Pragma_Is;

   ---------------------------------
   -- Get_Applicable_SPARK_Pragma --
   ---------------------------------

   function Get_Applicable_SPARK_Pragma
     (E       : Entity_Id;
      Is_Body : Boolean := False) return Node_Id is
   begin
      if Is_Body then
         if Applicable_SPARK_Mode_For_Body.Contains (E) then
            return Applicable_SPARK_Mode_For_Body.Element (E);
         else
            return Empty;
         end if;
      else
         if Applicable_SPARK_Mode_For_Spec.Contains (E) then
            return Applicable_SPARK_Mode_For_Spec.Element (E);
         else
            return Empty;
         end if;
      end if;
   end Get_Applicable_SPARK_Pragma;

   --------------------
   -- Get_Scope_Info --
   --------------------

   procedure Get_Scope_Info (N : Node_Id) is

      procedure Do_List (L : List_Id);
      --  Apply Get_Scope_Info to every element of list L

      procedure Push_SPARK_Pragma (Prag : Node_Id);
      --  If Prag is not Empty, push it on the stack of SPARK_Mode pragmas

      procedure Pop_SPARK_Pragma (Prag : Node_Id);
      --  If Prag is not Empty, pop it from the stack of SPARK_Mode pragmas

      procedure Store_Applicable_SPARK_Pragma
        (E       : Entity_Id;
         Is_Body : Boolean := False)
      with Pre => Ekind (E) /= E_Subprogram_Body;
      --  If SPARK_Mode_Pragmas_Stack is not empty, store its first element as
      --  the applicable SPARK_Mode pragma for E. If Is_Body is False, this
      --  applies to the spec view of entity E. If Is_Body is True, this
      --  applies to the body view of entity E. E need not be a unique entity.

      -------------
      -- Do_List --
      -------------

      procedure Do_List (L : List_Id) is
         N : Node_Id;
      begin
         N := First (L);
         while Present (N) loop
            Get_Scope_Info (N);
            Next (N);
         end loop;
      end Do_List;

      ----------------------
      -- Pop_SPARK_Pragma --
      ----------------------

      procedure Pop_SPARK_Pragma (Prag : Node_Id) is
      begin
         if Present (Prag) then
            pragma Assert (SPARK_Mode_Pragmas_Stack.First_Element = Prag);
            SPARK_Mode_Pragmas_Stack.Delete_First;
         end if;
      end Pop_SPARK_Pragma;

      -----------------------
      -- Push_SPARK_Pragma --
      -----------------------

      procedure Push_SPARK_Pragma (Prag : Node_Id) is
      begin
         if Present (Prag) then
            SPARK_Mode_Pragmas_Stack.Prepend (Prag);
         end if;
      end Push_SPARK_Pragma;

      -----------------------------------
      -- Store_Applicable_SPARK_Pragma --
      -----------------------------------

      procedure Store_Applicable_SPARK_Pragma
        (E       : Entity_Id;
         Is_Body : Boolean := False) is
      begin
         if not SPARK_Mode_Pragmas_Stack.Is_Empty then
            if Is_Body then
               Applicable_SPARK_Mode_For_Body.Insert
                 (E, SPARK_Mode_Pragmas_Stack.First_Element);
            else
               Applicable_SPARK_Mode_For_Spec.Insert
                 (E, SPARK_Mode_Pragmas_Stack.First_Element);
            end if;
         end if;
      end Store_Applicable_SPARK_Pragma;

      E        : Entity_Id;
      Unique_E : Entity_Id;
      Prag     : Node_Id;

   --  Start of Get_Scope_Info

   begin
      --  Get the applicable SPARK_Mode pragma for this unit, if any

      if Nkind (Parent (N)) = N_Compilation_Unit then

         --  ??? After Opt.Global_SPARK_Mode is changed to a Node_Id, this is
         --  the place to push it on the stack.

         Push_SPARK_Pragma
           (Lib.SPARK_Mode_Pragma (Lib.Get_Cunit_Unit_Number (Parent (N))));
      end if;

      --  Traversal currently stops at non-declarations (except
      --  N_Handled_Sequence_Of_Statements and N_Block_Statement which may
      --  contain declarations) which is sufficient to get the applicable
      --  SPARK_Mode pragma for each source entity.

      if Nkind (N) not in N_Declaration                    |
                          N_Later_Decl_Item                |
                          N_Handled_Sequence_Of_Statements |
                          N_Block_Statement
      then
         return;
      end if;

      --  ??? Currently ignore the exception handlers of the handled sequence
      --  of statements, which may contain declarations, and SPARK_Mode pragmas
      --  which should be checked. Change that when these declarations are
      --  marked for translation into Why.

      if Nkind (N) = N_Handled_Sequence_Of_Statements then
         Do_List (Statements (N));
         return;
      end if;

      if Nkind (N) = N_Block_Statement then
         Do_List (Declarations (N));
         Get_Scope_Info (Handled_Statement_Sequence (N));
         return;
      end if;

      --  Declarations which have no impact on SPARK_Mode stack

      if Nkind (N) in N_Renaming_Declaration        |
                      N_Implicit_Label_Declaration  |
                      N_Incomplete_Type_Declaration |
                      N_Use_Package_Clause
      then
         return;
      end if;

      --  ??? Currently ignore these declarations that are not in SPARK, even
      --  though they may contain declarations, and SPARK_Mode pragmas which
      --  should be checked. Change that when marking of these declarations
      --  takes place.

      if Nkind (N) in N_Entry_Declaration               |
                      N_Protected_Type_Declaration      |
                      N_Access_To_Subprogram_Definition |
                      N_Task_Type_Declaration           |
                      N_Body_Stub                       |
                      N_Generic_Instantiation           |
                      N_Protected_Body                  |
                      N_Task_Body                       |
                      N_Single_Task_Declaration         |
                      N_Generic_Package_Declaration     |
                      N_Generic_Subprogram_Declaration
      then
         return;
      end if;

      --  At this point, N is a declaration with an associated entity E. Note
      --  that E is not the unique entity here, as we are interested in
      --  information that may differ between the two views of a unique
      --  entity (package spec and package body for example). The corresponding
      --  unique entity is stored in Unique_E.

      E := Defining_Entity (N);
      Unique_E := Unique_Entity (E);

      --  Store the first applicable pragma in Prag, for every relevant entity

      if Ekind (E) in E_Function          |
                      E_Generic_Function  |
                      E_Generic_Procedure |
                      E_Procedure         |
                      E_Subprogram_Body   |
                      E_Generic_Package   |
                      E_Package           |
                      E_Package_Body
      then
         Prag := SPARK_Mode_Pragmas (E);
      end if;

      case Nkind (N) is
      when N_Package_Declaration =>
         declare
            Vis_Decls  : constant List_Id :=
              Visible_Declarations (Specification (N));
            Priv_Decls : constant List_Id :=
              Private_Declarations (Specification (N));
            Vis_Prag   : Node_Id := Empty;
            Priv_Prag  : Node_Id := Empty;

         begin
            --  Retrieve the SPARK_Mode pragmas on the visible and private
            --  parts of the package, if any.

            if Present (Prag)
              and then not Sem_Prag.Is_Private_SPARK_Mode (Prag)
            then
               Vis_Prag := Prag;
               Prag := Next_Pragma (Prag);
            end if;

            if Present (Prag) then
               pragma Assert (Sem_Prag.Is_Private_SPARK_Mode (Prag));
               Priv_Prag := Prag;
            end if;

            --  Do the package entity itself and its visible part

            Push_SPARK_Pragma (Vis_Prag);
            Store_Applicable_SPARK_Pragma (E);
            Do_List (Vis_Decls);

            --  Do the private part

            Push_SPARK_Pragma (Priv_Prag);
            Do_List (Priv_Decls);

            --  Pop the context

            Pop_SPARK_Pragma (Priv_Prag);
            Pop_SPARK_Pragma (Vis_Prag);
         end;

      when N_Package_Body =>
         declare
            Decls     : constant List_Id := Declarations (N);
            Stats     : constant Node_Id := Handled_Statement_Sequence (N);
            Decl_Prag : Node_Id := Empty;
            Stat_Prag : Node_Id := Empty;

         begin
            --  Do not analyze generic bodies

            if Ekind (Unique_E) = E_Generic_Package then
               return;
            end if;

            --  Retrieve the SPARK_Mode pragmas on the declarative and
            --  statement parts of the package body, if any.

            if Present (Prag)
              and then not Sem_Prag.Is_Elaboration_SPARK_Mode (Prag)
            then
               Decl_Prag := Prag;
               Prag := Next_Pragma (Prag);
            end if;

            if Present (Prag) then
               pragma Assert (Sem_Prag.Is_Elaboration_SPARK_Mode (Prag));
               Stat_Prag := Prag;
            end if;

            --  Do the package body entity itself and its declarative part

            Push_SPARK_Pragma (Decl_Prag);
            Store_Applicable_SPARK_Pragma (Unique_E, Is_Body => True);
            Do_List (Decls);

            --  Do the statement part

            Push_SPARK_Pragma (Stat_Prag);
            Get_Scope_Info (Stats);

            --  Pop the context

            Pop_SPARK_Pragma (Stat_Prag);
            Pop_SPARK_Pragma (Decl_Prag);
         end;

      when N_Subprogram_Declaration =>
         --  Do not analyze generics

         if Ekind (Unique_E) in Generic_Subprogram_Kind then
            return;
         end if;

         --  Do the subprogram declaration

         Push_SPARK_Pragma (Prag);
         Store_Applicable_SPARK_Pragma (E);

         --  For expression functions that have a unique declaration, treat the
         --  body here. See the case for N_Subprogram_Body below for details.

         if Present (Get_Expression_Function (E))
           and then not
             Comes_From_Source
               (Original_Node (SPARK_Util.Get_Subprogram_Body (E)))
         then
            Store_Applicable_SPARK_Pragma (E, Is_Body => True);
         end if;

         --  Pop the context

         Pop_SPARK_Pragma (Prag);

      when N_Subprogram_Body =>
         declare
            Decls : constant List_Id := Declarations (N);
            Stats : constant Node_Id := Handled_Statement_Sequence (N);

         begin
            --  Do not analyze generic bodies

            if Ekind (Unique_E) in Generic_Subprogram_Kind then
               return;
            end if;

            --  For expression functions that have a unique declaration, the
            --  body inserted by the frontend may be far from the original
            --  point of declaration, after the private declarations of the
            --  package (to avoid premature freezing.) In those cases, the
            --  subprogram body should be treated at the same point as the
            --  subprogram declaration, to avoid taking into account the
            --  SPARK_Mode set for the private part.

            if Present (Get_Expression_Function (Unique_E))
              and then not Comes_From_Source (Original_Node (N))
            then
               return;
            end if;

            --  Do the subprogram declaration if the body acts as spec

            Push_SPARK_Pragma (Prag);

            if Acts_As_Spec (N) then
               Store_Applicable_SPARK_Pragma (Unique_E);
            end if;

            --  Do the subprogram body itself, its declarations and statements

            Store_Applicable_SPARK_Pragma (Unique_E, Is_Body => True);
            Do_List (Decls);
            Get_Scope_Info (Stats);

            --  Pop the context

            Pop_SPARK_Pragma (Prag);
         end;

      when N_Object_Declaration =>
         declare
            Is_Body : constant Boolean := Is_Full_View (E);

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

            Store_Applicable_SPARK_Pragma (Unique_E, Is_Body => Is_Body);
         end;

      when N_Subtype_Declaration           |
           N_Full_Type_Declaration         |
           N_Private_Type_Declaration      |
           N_Private_Extension_Declaration =>
         declare
            Is_Body : constant Boolean := Is_Full_View (E);

         begin
            --  Store correspondance from completions of private types, so that
            --  Is_Full_View can be used for dealing correctly with private
            --  types, when the public part of the package is marked as
            --  SPARK_Mode On, and the private part of the package is marked
            --  as SPARK_Mode Off. This is also used later during generation
            --  of Why.

            if Ekind (E) in Private_Kind
              and then Present (Full_View (E))
            then
               Add_Full_And_Partial_View (Full_View (E), E);
            end if;

            Store_Applicable_SPARK_Pragma (Unique_E, Is_Body => Is_Body);
         end;

      when others =>
         Ada.Text_IO.Put_Line ("[Get_Scope_Info] kind ="
                                & Node_Kind'Image (Nkind (N)));
         raise Program_Error;
      end case;
   end Get_Scope_Info;

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

   --  If the entity is defined in the spec or the body of the current compiled
   --  unit, it is added to one of the list of entities Spec_Entities or
   --  Body_Entities, which will be translated to Why3. The translation
   --  will depend on the status (in SPARK or not) of each entity.

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

   ------------------------------------
   -- Stack of Entities Being Marked --
   ------------------------------------

   --  Entities being marked are recorded in a stack, where the first element
   --  represents the most recent entity being considered. Matching calls to
   --  Puch_Entity and Pop_Entity add and remove from this stack. A view of the
   --  stack as a set is maintained in parallel, as this is more efficient
   --  for testing recursion. Another stack is formed by the subset of these
   --  entities which are the "visible" ones, used for reporting errors.

   --  The possible kinds of entities on the stack are:
   --  . a package
   --  . a subprogram
   --  . a variable
   --  . a type

   Entity_Stack          : List_Of_Nodes.List;
   Entity_Stack_As_A_Set : Node_Sets.Set;
   Visible_Entity_Stack  : List_Of_Nodes.List;

   In_Toplevel_Subprogram_Body : Boolean := False;
   --  Flag set when making the body of a toplevel subprogram

   function Current_Entity return Entity_Id;
   --  Returns the current entity on which to attach violations of SPARK.

   function Current_Toplevel_Entity return Entity_Id;
   --  Returns the current "visible" entity on which to attach violations of
   --  SPARK.

   function In_Entity_Stack (E : Entity_Id) return Boolean;
   --  Returns True if E belongs to the set of entities currently being marked

   procedure Push_Entity (E : Entity_Id);
   --  Set entity E as the top one in the stack

   procedure Pop_Entity (E : Entity_Id);
   --  Remove the top entity in the stack, which should match with entity E

   procedure Push_Toplevel_Subprogram_Body (E : Entity_Id);
   --  Set entity E as the top one in the stack, and set
   --  In_Toplevel_Subprogram_Body to True.

   procedure Pop_Toplevel_Subprogram_Body (E : Entity_Id);
   --  Remove the top entity in the stack, which should match with entity E,
   --  and set In_Toplevel_Subprogram_Body to False.

   --------------------
   -- Current_Entity --
   --------------------

   function Current_Entity return Entity_Id is
     (if not Entity_Stack.Is_Empty then
        Entity_Stack.First_Element
      else
        Empty);

   -----------------------------
   -- Current_Toplevel_Entity --
   -----------------------------

   function Current_Toplevel_Entity return Entity_Id is
     (if not Visible_Entity_Stack.Is_Empty then
        Visible_Entity_Stack.First_Element
      else
        Empty);

   ---------------------
   -- In_Entity_Stack --
   ---------------------

   function In_Entity_Stack (E : Entity_Id) return Boolean is
   begin
      return Entity_Stack_As_A_Set.Contains (E);
   end In_Entity_Stack;

   ----------------
   -- Pop_Entity --
   ----------------

   procedure Pop_Entity (E : Entity_Id) is
   begin
      pragma Assert (Entity_Stack.First_Element = E);
      Entity_Stack.Delete_First;
      Entity_Stack_As_A_Set.Delete (E);

      if not In_Toplevel_Subprogram_Body then
         pragma Assert (Visible_Entity_Stack.First_Element = E);
         Visible_Entity_Stack.Delete_First;
      end if;
   end Pop_Entity;

   ----------------------------------
   -- Pop_Toplevel_Subprogram_Body --
   ----------------------------------

   procedure Pop_Toplevel_Subprogram_Body (E : Entity_Id) is
   begin
      pragma Assert (In_Toplevel_Subprogram_Body);
      In_Toplevel_Subprogram_Body := False;
      Pop_Entity (E);
   end Pop_Toplevel_Subprogram_Body;

   -----------------
   -- Push_Entity --
   -----------------

   procedure Push_Entity (E : Entity_Id) is
   begin
      Entity_Stack.Prepend (E);
      Entity_Stack_As_A_Set.Insert (E);

      if In_Toplevel_Subprogram_Body then
         pragma Assert (not Is_Toplevel_Entity (E));

      else
         Visible_Entity_Stack.Prepend (E);
      end if;
   end Push_Entity;

   -----------------------------------
   -- Push_Toplevel_Subprogram_Body --
   -----------------------------------

   procedure Push_Toplevel_Subprogram_Body (E : Entity_Id) is
   begin
      pragma Assert (not In_Toplevel_Subprogram_Body);
      Push_Entity (E);
      In_Toplevel_Subprogram_Body := True;
   end Push_Toplevel_Subprogram_Body;

   -------------------------------------
   -- Adding Entities for Translation --
   -------------------------------------

   --  There are two possibilities when marking an entity, depending on whether
   --  this is in the context of a toplevel subprogram body or not. In the
   --  first case, violations are directly attached to the toplevel subprogram
   --  entity, and local entities are added or not as a whole, after the
   --  subprogram body has been fully marked. In the second case, violations
   --  are attached to the entity itself, which is directly added to the lists
   --  for translation after marking.

   Subprogram_Entities : List_Of_Nodes.List;
   --  List of entities declared locally in the toplevel subprogram body

   Current_Unit_Is_Main_Body : Boolean;
   --  Flag set when marking the body for the current compiled unit

   Current_Unit_Is_Main_Spec : Boolean;
   --  Flag set when marking the spec for the current compiled unit

   Entities_In_SPARK : Node_Sets.Set;
   --  Entities in SPARK. An entity is inserted in this set if, after marking,
   --  no violations where attached to the corresponding scope. Standard
   --  entities are individually added to this set.

   Bodies_In_SPARK   : Node_Sets.Set;
   --  Subprogram entities whose body is in SPARK. An entity is inserted
   --  in this set if, after marking, no violations where attached to the
   --  corresponding body scope.

   procedure Append_Entity_To_List (E : Entity_Id);
   --  Append entity E to the appropriate list for translation to Why

   procedure Append_Subprogram_Entities_To_List;
   --  Append all entities locally defined in the current toplevel subprogram
   --  body to the appropriate list for translation to Why. This is called
   --  after marking a toplevel subprogram body, if this body is in SPARK, to
   --  add all local entities for translation.

   function Entity_In_SPARK (E : Entity_Id) return Boolean is
     (Entities_In_SPARK.Contains (E));

   function Subprogram_Body_In_SPARK (E : Entity_Id) return Boolean is
     (Bodies_In_SPARK.Contains (E));

   ---------------------------
   -- Append_Entity_To_List --
   ---------------------------

   procedure Append_Entity_To_List (E : Entity_Id) is
   begin
      --  Local entities to a toplevel subprogram body are temporarily stored
      --  in Subprogram_Entities.

      if In_Toplevel_Subprogram_Body then
         Subprogram_Entities.Append (E);

      --  Outside of a toplevel subprogram body, entities from the current unit
      --  are added either to Spec_Entities or Body_Entities, depending on
      --  whether they belong to the current unit spec or current unit body.

      elsif Current_Unit_Is_Main_Spec then
         Spec_Entities.Append (E);

      elsif Current_Unit_Is_Main_Body then
         Body_Entities.Append (E);
      end if;
   end Append_Entity_To_List;

   ----------------------------------------
   -- Append_Subprogram_Entities_To_List --
   ----------------------------------------

   procedure Append_Subprogram_Entities_To_List is
   begin
      --  If the subprogram body is defined in the current unit spec (case of
      --  expression functions), then all local entities are added to
      --  Spec_Entities.

      if Current_Unit_Is_Main_Spec then
         for E of Subprogram_Entities loop
            Spec_Entities.Append (E);
         end loop;

      --  In the general case where the subprogram body is defined in the
      --  current unit body, all local entities are added to Body_Entities.

      elsif Current_Unit_Is_Main_Body then
         for E of Subprogram_Entities loop
            Body_Entities.Append (E);
         end loop;
      end if;

      Subprogram_Entities.Clear;
   end Append_Subprogram_Entities_To_List;

   ----------------------
   -- SPARK Violations --
   ----------------------

   --  SPARK violations are recorded for toplevel entities only, for which the
   --  decision to translate them to Why is taken separately. This is not the
   --  case for all local declarations in subprograms, which are only
   --  translated if the complete subprogram body is in SPARK.

   --  Not only the presence of a violation is recorded, but the kind of
   --  violation, in order to be able to generate a percentage of subprograms
   --  not in SPARK per kind of violation.

   --  If a toplevel entity has an applicable pragma SPARK_Mode On, any SPARK
   --  violation is reported as an error.

   type Violations is array (SPARK_Violations.Vkind) of Node_Sets.Set;

   Spec_Violations : Violations;
   --  Sets of entities which violate SPARK restrictions, per violation kind

   Body_Violations : Violations;
   --  Sets of subprogram entities whose body violate SPARK restrictions, per
   --  violation kind.

   procedure Mark_Violation
     (Msg : String;
      N   : Node_Id;
      V   : SPARK_Violations.Vkind);
   --  Mark node N as a violation of SPARK. The violation is attached to all
   --  entities in the current entity stack. A message is also issued in some
   --  cases.

   procedure Mark_Violation
     (Msg  : String;
      N    : Node_Id;
      From : Entity_Id);
   --  Similar to the previous one, except here violations are inherited from
   --  entity From.

   procedure Inherit_Violations
     (A        : in out Violations;
      To, From : Entity_Id);
   --  Make To inherit the violations of From in Violations

   function Has_Violations (Id : Entity_Id) return Boolean;
   --  Return whether a violation of SPARK was detected while analyzing the
   --  definition of entity Id. This does not include violations in the body of
   --  a subprogram, which are recorded separately.

   function Has_Body_Violations (Id : Entity_Id) return Boolean;
   --  Return whether a violation of SPARK was detected while analyzing the
   --  body of subprogram Id.

   function Complete_Error_Msg
     (Msg : String;
      V   : SPARK_Violations.Vkind) return String;
   --  Generate a message for SPARK violations, which may be an error, a
   --  warning or an info message depending on the analysis mode and the
   --  violation.

   ------------------------
   -- Complete_Error_Msg --
   ------------------------

   function Complete_Error_Msg
     (Msg : String;
      V   : SPARK_Violations.Vkind) return String
   is
      --  When reporting a forward reference, this takes priority over the
      --  default reason for not being in SPARK (e.g. "subprogram called")

      Use_Msg : constant String :=
                  (if V = NIR_Forward_Reference then
                     "forward reference"
                   else Msg);
   begin
      case V is
         when SPARK_Violations.Not_In_Roadmap =>
            return Use_Msg & " is not in 'S'P'A'R'K";

         when SPARK_Violations.Not_Yet_Implemented =>
            return Use_Msg & "? is not yet supported";
      end case;
   end Complete_Error_Msg;

   -------------------------
   -- Has_Body_Violations --
   -------------------------

   function Has_Body_Violations (Id : Entity_Id) return Boolean is
     (for some S of Body_Violations => S.Contains (Id));

   --------------------
   -- Has_Violations --
   --------------------

   function Has_Violations (Id : Entity_Id) return Boolean is
     (for some S of Spec_Violations => S.Contains (Id));

   ------------------------
   -- Inherit_Violations --
   ------------------------

   procedure Inherit_Violations
     (A        : in out Violations;
      To, From : Entity_Id)
   is
   begin
      --  If From was explicitly marked as not in SPARK, inherit the reason for
      --  not being in SPARK.

      if (for some S of Spec_Violations => S.Contains (From)) then
         for V in SPARK_Violations.Vkind loop
            if Spec_Violations (V).Contains (From) then
               A (V).Include (To);
            end if;
         end loop;

      --  If From was not yet marked, this is a forward reference (or currently
      --  an entity defined in a task, which is not marked, to be refined
      --  later.)

      else
         pragma Assert (not All_Entities.Contains (From));
         A (NIR_Forward_Reference).Include (To);
      end if;
   end Inherit_Violations;

   --------------------
   -- Mark_Violation --
   --------------------

   procedure Mark_Violation
     (Msg    : String;
      N      : Node_Id;
      V      : SPARK_Violations.Vkind)
   is
      E       : constant Entity_Id := Current_Toplevel_Entity;
      Is_Body : constant Boolean := In_Toplevel_Subprogram_Body;

   begin
      pragma Assert (Present (E));

      --  Raise an error if the violation is forbidden by the use of pragma
      --  SPARK_Mode with value On.

      if Applicable_SPARK_Pragma_Is (E, SPARK_On, Is_Body) then
         Error_Msg_F (Complete_Error_Msg (Msg, V), N);
      end if;

      --  Store the violation with the corresponding toplevel entity

      if In_Toplevel_Subprogram_Body then
         Body_Violations (V).Include (E);
      else
         Spec_Violations (V).Include (E);
      end if;

      --  Also record that the current entity is not in SPARK. This is in
      --  particular needed for class-wide types, which may be seen in the
      --  context of different toplevel entities. So marking the first toplevel
      --  entity as not SPARK is not sufficient, as the class-wide type has now
      --  been marked as seen, but it is also visible in the context of other
      --  toplevel entities, where it should be known to be not in SPARK.

      Spec_Violations (V).Include (Current_Entity);
   end Mark_Violation;

   procedure Mark_Violation
     (Msg  : String;
      N    : Node_Id;
      From : Entity_Id)
   is
      E       : constant Entity_Id := Current_Toplevel_Entity;
      Is_Body : constant Boolean := In_Toplevel_Subprogram_Body;

   begin
      pragma Assert (Present (E));

      --  Raise an error if the violation is forbidden by the use of pragma
      --  SPARK_Mode with value On.

      if Applicable_SPARK_Pragma_Is (E, SPARK_On, Is_Body) then

         if In_Standard_Scope (From)
           or else Spec_Violations (NIR_XXX).Contains (From)
         then
            Error_Msg_F (Complete_Error_Msg (Msg, NIR_XXX), N);

         elsif (for some V in SPARK_Violations.Not_In_Roadmap =>
                  Spec_Violations (V).Contains (From))
         then
            for V in SPARK_Violations.Not_In_Roadmap loop
               if Spec_Violations (V).Contains (From) then
                  Error_Msg_F (Complete_Error_Msg (Msg, V), N);
               end if;
            end loop;

         elsif (for some V in SPARK_Violations.Not_Yet_Implemented =>
                  Spec_Violations (V).Contains (From))
         then
            for V in SPARK_Violations.Not_Yet_Implemented loop
               if Spec_Violations (V).Contains (From) then
                  Error_Msg_F (Complete_Error_Msg (Msg, V), N);
               end if;
            end loop;

         else
            Error_Msg_F (Complete_Error_Msg (Msg, NIR_Forward_Reference), N);
         end if;
      end if;

      --  Store the violation with the corresponding toplevel entity

      if In_Toplevel_Subprogram_Body then
         Inherit_Violations (Body_Violations, From => From, To => E);
      else
         Inherit_Violations (Spec_Violations, From => From, To => E);
      end if;

      --  Also record that the current entity is not in SPARK. This is in
      --  particular needed for class-wide types, which may be seen in the
      --  context of different toplevel entities. So marking the first toplevel
      --  entity as not SPARK is not sufficient, as the class-wide type has now
      --  been marked as seen, but it is also visible in the context of other
      --  toplevel entities, where it should be known to be not in SPARK.

      Inherit_Violations (Spec_Violations, From => From, To => Current_Entity);
   end Mark_Violation;

   ------------------------------
   -- Output SPARK Information --
   ------------------------------

   procedure Generate_Output_In_Out_SPARK (Id : Entity_Id);
   --  Produce a line in output file for subprogram Id, following syntax:
   --
   --    cd name location opt_list_NIR opt_list_NYI
   --
   --  where
   --
   --    c and d are characters which denote respectively whether the body and
   --    spec of subprogram Id are:
   --      + in SPARK
   --      - not in SPARK roadmap
   --      * not yet implemented in SPARK
   --
   --    name is the name of subprogram Id
   --    location is the location (file:line) of subprogram Id
   --
   --    opt_list_NIR and opt_list_NYI are optional lists of violations of
   --    SPARK for not-in-roadmap constructs (NIR) or not-yet-implemented
   --    constructs (NYI). opt_list_NIR is enclosed in parentheses.
   --    opt_list_NYI is enclosed in brackets. Both are comma-separated lists.
   --
   --  examples:
   --
   --  -+ pack__f f.adb:3 (tasking)
   --  Subprogram Pack.F has its spec in SPARK, and its body not in SPARK, due
   --  to the use of tasking.
   --
   --  ++ pack__g f.adb:78
   --  Subprogram Pack.G is in SPARK
   --
   --  ** pack__h f.adb:3 [slice, not yet implemented]
   --  Subprogram Pack.H has both its spec and body not implemented in SPARK,
   --  due to the use of slices, plus some other not precised constructs.

   Output_File : Ada.Text_IO.File_Type;
   --  <file>.alfa in which this pass generates information about subprograms
   --  in SPARK and subprograms not in SPARK.

   -------------------
   -- After_Marking --
   -------------------

   procedure After_Marking is
   begin
      Close (Output_File);
   end After_Marking;

   --------------------
   -- Before_Marking --
   --------------------

   procedure Before_Marking (Filename : String) is
   begin
      Create (Output_File, Out_File, Filename);
   end Before_Marking;

   ----------------------------------
   -- Generate_Output_In_Out_SPARK --
   ----------------------------------

   procedure Generate_Output_In_Out_SPARK (Id : Entity_Id) is
      generic
         type Violation_Subkind is (<>);
         Open, Close : Character;
         with function Has_Violation
           (V : Violation_Subkind;
            E : Entity_Id) return Boolean is <>;
         with function Get_Violation_Msg
           (V : Violation_Subkind) return Unbounded_String is <>;
      function Collect_Msg_Violations
        (E : Entity_Id) return String;
      --  Produce a comma-separated list of message for NYI or NIR violations,
      --  enclosed in Open-Close characters.

      function Suffix return String;
      --  Suffix string indicates why subprogram body is not in SPARK

      ----------------------
      -- Helper Functions --
      ----------------------

      function Has_Violation
        (V : SPARK_Violations.Vkind;
         E : Entity_Id) return Boolean
      is
        (Body_Violations (V).Contains (E));

      function Get_Violation_Msg
        (V : SPARK_Violations.Vkind) return Unbounded_String
      is
        (SPARK_Violations.Violation_Msg (V));

      function Location return String is
        (Name_String (Chars (Id)) & ' ' & Build_Location_String (Sloc (Id)));
      --  Location string points to source location for entity. Use the
      --  location of the body (Defining_Entity) rather than the location
      --  of the spec (Id).

      ----------------------------
      -- Collect_Msg_Violations --
      ----------------------------

      function Collect_Msg_Violations
        (E : Entity_Id) return String
      is
         Msg : Unbounded_String;
      begin
         for V in Violation_Subkind loop
            if Has_Violation (V, E) then
               if Msg = "" then
                  Msg := Msg & Get_Violation_Msg (V);
               else
                  Msg := Msg & ", " & Get_Violation_Msg (V);
               end if;
            end if;
         end loop;

         if Msg /= "" then
            return Open & To_String (Msg) & Close;
         else
            return "";
         end if;
      end Collect_Msg_Violations;

      --------------------------------------
      -- Collect_Msg_Violations Instances --
      --------------------------------------

      function Collect_NYI_Msg_Violations is
        new Collect_Msg_Violations
          (SPARK_Violations.Not_Yet_Implemented, '[', ']');

      function Collect_NIR_Msg_Violations is
        new Collect_Msg_Violations (SPARK_Violations.Not_In_Roadmap, '(', ')');

      ------------
      -- Suffix --
      ------------

      function Suffix return String is
      begin
         if Subprogram_Body_In_SPARK (Id) then
            return "";
         else
            declare
               NIR_Msg : constant String :=
                           Collect_NIR_Msg_Violations (Id);
               NYI_Msg : constant String :=
                           Collect_NYI_Msg_Violations (Id);
            begin
               if NIR_Msg /= "" and then NYI_Msg /= "" then
                  return ' ' & NIR_Msg & ' ' & NYI_Msg;
               elsif NIR_Msg /= "" then
                  return ' ' & NIR_Msg;
               elsif NYI_Msg /= "" then
                  return ' ' & NYI_Msg;
               elsif Applicable_SPARK_Pragma_Is
                 (Id, SPARK_Off, Is_Body => True)
               then
                  return " SPARK_Mode=Off";
               else
                  raise Program_Error;
               end if;
            end;
         end if;
      end Suffix;

      C1, C2 : Character;
      --  Character indicates whether entity body (C1) and spec (C2) are:
      --    + in SPARK
      --    - not in SPARK roadmap
      --    * not yet implemented in SPARK

   begin
      if Comes_From_Source (Id) then
         if Subprogram_Body_In_SPARK (Id) then
            C1 := '+';
         elsif (for some V in SPARK_Violations.Not_In_Roadmap =>
                   Body_Violations (V).Contains (Id)) then
            C1 := '-';
         else
            C1 := '*';
         end if;

         if Entity_In_SPARK (Id) then
            C2 := '+';
         elsif (for some V in SPARK_Violations.Not_In_Roadmap =>
                   Spec_Violations (V).Contains (Id)) then
            C2 := '-';
         else
            C2 := '*';
         end if;

         Put_Line (Output_File, C1 & C2 & ' ' & Location & Suffix);
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
   --  adds E to the set of All_Entities as a result. If no violation was
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
      --  If the entity is already present in the set of entities being
      --  currently marked, consider it is in SPARK. If not, this will be
      --  detected through an actual violation.

      if In_Entity_Stack (E) then
         return True;

      --  In the normal case, mark the entity, and return the result of
      --  marking stored in Entities_In_SPARK.

      else
         Mark_Entity (E);
         return Entities_In_SPARK.Contains (E);
      end if;
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
            Mark_Violation ("type", N, From => T);
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

      begin
         --  The object is in SPARK if-and-only-if its type is in SPARK, it
         --  is not aliased, and its initialization expression, if any, is
         --  in SPARK.

         if not In_SPARK (T) then
            Mark_Violation ("type", Def, From => T);
         end if;

         if Aliased_Present (N) then
            Mark_Violation ("ALIASED", N, NIR_Access);
         end if;

         if Present (Expr) then
            Mark (Expr);
         end if;
      end Mark_Object_Entity;

      ---------------------------
      -- Mark_Parameter_Entity --
      ---------------------------

      procedure Mark_Parameter_Entity (E : Entity_Id) is
      begin
         if not In_SPARK (Etype (E)) then
            Mark_Violation ("type", E, From => Etype (E));
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
            if Has_Global_Writes (Id) then
               Mark_Violation
                 ("function with side-effects", Id, NIR_Impure_Function);
               return;
            end if;

            if Is_Non_Empty_List (Params) then
               Param := First (Params);
               while Present (Param) loop
                  Param_Id := Defining_Identifier (Param);

                  case Ekind (Param_Id) is
                  when E_Out_Parameter =>
                     Mark_Violation ("function with OUT parameter", Id,
                                     NIR_Impure_Function);
                     return;
                  when E_In_Out_Parameter =>
                     Mark_Violation ("function with IN OUT parameter", Id,
                                     NIR_Impure_Function);
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
                     Mark_Violation ("type", E, From => Etype (Formal));
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
               Mark_Violation
                 ("return type", Result_Definition (N), From => Etype (Id));
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
      begin
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
            Mark_Entity (Underlying_Type (E));

         when others =>
            null;
         end case;

         --  Now mark the type itself

         --  Special case to accept subtypes and derived types of formal
         --  container types.

         if Type_Based_On_Formal_Container (E) then
            return;
         end if;

         if Is_Tagged_Type (E) then
            Mark_Violation ("tagged type", E, NYI_Tagged);
         end if;

         if Has_Invariants (E) then
            Mark_Violation ("type invariant", E, NYI_Invariant);
         end if;

         if Has_Predicates (E) then
            Mark_Violation ("type predicate", E, NYI_Predicate);
         end if;

         case Ekind (E) is
         when Array_Kind =>
            declare
               Component_Typ : constant Node_Id := Component_Type (E);
               Index         : Node_Id := First_Index (E);

            begin
               --  Currently, array types of dimension 4 at most are supported

               if Number_Dimensions (E) > 4 then
                  Mark_Violation ("array type", E, NYI_Multi_Dim_Array);
               end if;

               --  Check that all index types are in SPARK

               while Present (Index) loop
                  if not In_SPARK (Etype (Index)) then
                     Mark_Violation
                       ("index type", E, From => Etype (Index));
                  end if;
                  Next_Index (Index);
               end loop;

               --  Access definition for component type is not in SPARK

               if No (Component_Typ) then
                  Mark_Violation ("access type", E, NIR_Access);
               end if;

               --  Check that component type is in SPARK. There is a special
               --  case for component types from formal containers, as
               --  node_type is not in SPARK, but we still want arrays of these
               --  to be considered in SPARK, as they are implicitly declared
               --  by the frontend when declaring a subtype of a formal
               --  container type.

               if not In_SPARK (Component_Typ)
                 and not
                   Location_In_Formal_Containers (Sloc (Etype (Component_Typ)))
               then
                  Mark_Violation
                    ("component type", E, From => Component_Typ);
               end if;
            end;

            --  Scalar types are always in SPARK

         when Integer_Kind | Real_Kind | Enumeration_Kind =>
            null;

         when E_Record_Type | E_Record_Subtype =>

            if Ekind (E) = E_Record_Subtype
              and then not In_SPARK (Base_Type (E))
            then
               Mark_Violation ("base type", E, From => Base_Type (E));
            end if;

            if Is_Interface (E) then
               Mark_Violation ("interface", E, NYI_Interface);

            else
               declare
                  Field : Node_Id := First_Component_Or_Discriminant (E);
                  Typ   : Entity_Id;

               begin
                  while Present (Field) loop
                     Typ := Etype (Field);

                     if Is_Tag (Field) then
                        Mark_Violation ("tagged type", E, NYI_Tagged);
                     elsif Is_Aliased (Field) then
                        Mark_Violation ("ALIASED", Field, NIR_Access);
                     end if;

                     if Ekind (Field) in Object_Kind
                       and then not In_SPARK (Typ)
                     then
                        Mark_Violation ("component type", Typ, From => Typ);
                     end if;

                     Next_Component_Or_Discriminant (Field);
                  end loop;
               end;
            end if;

         when E_Class_Wide_Type    |
              E_Class_Wide_Subtype =>
            Mark_Violation ("type definition", E, NYI_Class_Wide);

         when Access_Kind =>
            Mark_Violation ("access type", E, NIR_Access);

         when Concurrent_Kind =>
            Mark_Violation ("tasking", E, NIR_Tasking);

         when Private_Kind =>

            --  Private types that are not a record type or subtype are in
            --  SPARK.

            if Ekind_In (E, E_Record_Type_With_Private,
                         E_Record_Subtype_With_Private)
            then
               Mark_Violation ("type definition", E, NYI_Tagged);
            end if;

         when others =>
            raise Program_Error;
         end case;
      end Mark_Type_Entity;

   --  Start of Mark_Entity

   begin
      pragma Assert (not In_Entity_Stack (E));

      --  Nothing to do if the entity E was already marked

      if All_Entities.Contains (E) then
         return;
      end if;

      --  ??? In rare cases, like renaming of imported C functions, the code
      --  may refer to toplevel entities which have not been marked. Currently
      --  raise a violation in that case instead of failing inside Push_Entity.

      if In_Toplevel_Subprogram_Body
        and then Is_Toplevel_Entity (E)
      then
         Mark_Violation ("entity", E, NIR_Forward_Reference);
         goto After_Violations;
      end if;

      --  Push entity E on the entity stack, to detect recursion and report
      --  violations.

      Push_Entity (E);

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

                  --  ??? This should not happen, as the frontend should be
                  --  rewriting all renamings to refer to the renamed variable.
                  --  Currently raise a violation instead of failing, which
                  --  occurs on the standard library.

                  when N_Object_Renaming_Declaration =>
                     Mark_Violation ("entity", E, NIR_Forward_Reference);

                  when others                   => raise Program_Error;
               end case;
            end;
         when E_Loop_Parameter |
              Formal_Kind      => Mark_Parameter_Entity (E);
         when Named_Kind       => Mark_Number_Entity (E);

         --  The identifier of a loop is used to generate the needed exception
         --  declarations in the translation phase.

         when E_Loop           => null;

         when others           =>
            Ada.Text_IO.Put_Line ("[Mark_Entity] kind ="
                                  & Entity_Kind'Image (Ekind (E)));
            raise Program_Error;
      end case;

      --  Pop entity E from the entity stack

      Pop_Entity (E);

      <<After_Violations>>

      --  Mark entity E as being in SPARK if no violation was detected

      if not Has_Violations (E) then
         Entities_In_SPARK.Include (E);
      end if;

      --  Add entity to appropriate list, except for types defined in formal
      --  container instances, which should be translated specially to Why.

      if not (Ekind (E) in Type_Kind
                and then Type_In_Formal_Container (E))
      then
         Append_Entity_To_List (E);
      end if;

      --  Include entity E in the set of entities marked

      All_Entities.Insert (E);
   end Mark_Entity;

   ----------
   -- Mark --
   ----------

   procedure Mark (N : Node_Id) is
   begin
      --  If present, the type of N should be in SPARK. This also allows
      --  marking Itypes and class-wide types at their first occurrence
      --  (inside In_SPARK).

      if Nkind (N) in N_Has_Etype
        and then not In_SPARK (Etype (N))
      then
         Mark_Violation ("type used", N, From => Etype (N));
      end if;

      --  Dispatch on node kind

      case Nkind (N) is

         when N_Abstract_Subprogram_Declaration =>
            Mark_Violation ("abstract subprogram", N, NYI_Tagged);

         when N_Aggregate =>

            --  Aggregates should be completely initialized to
            --  be in SPARK, otherwise they do not have a logic interpretation.

            if not Aggregate_Is_Fully_Initialized (N) then
               Mark_Violation ("aggregate not fully initialized",
                               N, NIR_Uninit_Logic_Expr);
            end if;

            Mark_Most_Underlying_Type_In_SPARK (Etype (N), N);
            Mark_List (Expressions (N));
            Mark_List (Component_Associations (N));

         when N_Allocator =>
            Mark_Violation ("allocator", N, NIR_Dynamic_Alloc);

         when N_Assignment_Statement =>
            Mark (Name (N));
            Mark (Expression (N));

         when N_At_Clause =>
            Mark_Violation ("at clause", N, NYI_Rep_Clause);

         when N_Attribute_Reference =>
            Mark_Attribute_Reference (N);

         when N_Attribute_Definition_Clause   =>
            Mark_Violation ("attribute definition clause", N, NYI_Rep_Clause);

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
            Mark_Violation ("code statement", N, NIR_Assembly_Lang);

         when N_Component_Association =>
            pragma Assert (No (Loop_Actions (N)));
            Mark_List (Choices (N));
            if not Box_Present (N) then
               Mark (Expression (N));
            end if;

         when N_Component_Declaration =>
            Mark_Component_Declaration (N);

         when N_Enumeration_Representation_Clause =>
            Mark_Violation
              ("enumeration representation clause", N, NYI_Rep_Clause);

         when N_Exception_Declaration          |
              N_Exception_Renaming_Declaration =>
            Mark_Violation ("exception", N, NIR_Exception);

         when N_Exit_Statement =>
            if Present (Condition (N)) then
               Mark (Condition (N));
            end if;

         when N_Expanded_Name =>
            Mark_Identifier_Or_Expanded_Name (N);

         when N_Explicit_Dereference =>
            Mark_Violation ("explicit dereference", N, NIR_Access);

         when N_Extended_Return_Statement =>
            Mark_Violation ("extended RETURN", N, NYI_Extended_Return);

         when N_Extension_Aggregate =>
            Mark_Violation ("extension aggregate", N, NYI_Aggregate);

         when N_Free_Statement =>
            Mark_Violation ("free statement", N, NIR_Dealloc);

         when N_Function_Call =>
            Mark_Call (N);

         when N_Goto_Statement =>
            Mark_Violation ("goto statement", N, NIR_Goto);

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
            --  The loop parameter shall be added to the entities in SPARK

            declare
               Loop_Index : constant Entity_Id := Defining_Identifier (N);
            begin
               Mark_Entity (Loop_Index);
            end;

            if Present (Subtype_Indication (N)) then
               Mark (Subtype_Indication (N));
            end if;

            if Is_Array_Type (Etype (Name (N))) then
               Mark_Violation
                 ("iterator on array type", N, NYI_Array_Operation);
            end if;

            --  Treat specially the case of X.Iterate for X a formal container,
            --  so that the iterator type is ignored instead of being
            --  identified as a violation of SPARK.

            declare
               Iter : constant Node_Id := Name (N);
            begin
               if Nkind (Iter) = N_Function_Call
                 and then Is_Entity_Name (Name (Iter))
                 and then
                   Ada.Strings.Fixed.Translate
                     (Get_Name_String (Chars (Name (Iter))),
                      Ada.Strings.Maps.Constants.Lower_Case_Map) =
                   SPARK_Util.Lowercase_Iterate_Name
                 and then
                   Location_In_Formal_Containers (Sloc (Entity (Name (Iter))))
               then
                  Mark_List (Parameter_Associations (Iter));
               else
                  Mark (Name (N));
               end if;
            end;

         when N_Loop_Statement =>
            --  Mark the entity for the loop, which is used in the translation
            --  phase to generate exceptions for this loop.

            Mark_Entity (Entity (Identifier (N)));

            if Present (Iteration_Scheme (N)) then
               Mark_Iteration_Scheme (Iteration_Scheme (N));
            end if;
            Mark_List (Statements (N));

         when N_Membership_Test =>
            if Is_Array_Type (Etype (Left_Opnd (N))) then
               Mark_Violation
                 ("membership on array type", N, NYI_Array_Operation);
            end if;
            Mark (Left_Opnd (N));
            if Present (Alternatives (N)) then
               Mark_List (Alternatives (N));
            else
               Mark (Right_Opnd (N));
            end if;

         when N_Null =>
            Mark_Violation ("null", N, NIR_Access);

         when N_Number_Declaration =>
            Mark_Number_Declaration (N);

         when N_Object_Declaration =>
            Mark_Object_Declaration (N);

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
            Mark_Violation ("raise statement", N, NIR_Exception);

         when N_Raise_Expression =>
            Mark_Violation ("raise expression", N, NIR_Exception);

         when N_Range =>
            Mark (Low_Bound (N));
            Mark (High_Bound (N));

         when N_Record_Representation_Clause =>
            Mark_Violation ("record representation clause", N, NYI_Rep_Clause);

         when N_Reference =>
            Mark_Violation ("reference", N, NIR_Access);

         when N_Short_Circuit =>
            Mark_Actions (N, Actions (N));
            Mark (Left_Opnd (N));
            Mark (Right_Opnd (N));

         when N_Simple_Return_Statement =>
            Mark_Simple_Return_Statement (N);

         when N_Selected_Component =>
            Mark_Most_Underlying_Type_In_SPARK (Etype (Prefix (N)), N);
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
            if Is_Composite_Type (Entity (Subtype_Mark (N))) then
               if Etype (Expression (N)) = Entity (Subtype_Mark (N)) then
                  Mark (Expression (N));
               else
                  Mark_Violation ("conversion between composite types", N,
                                  NYI_Composite_Conv);
               end if;
            else
               Mark (Expression (N));
            end if;

         when N_Unary_Op =>
            Mark_Unary_Op (N);

         when N_Unchecked_Expression =>
            Mark_Violation ("unchecked expression", N, NYI_Unchecked);

         when N_Unchecked_Type_Conversion =>
            if Comes_From_Source (N) then
               Mark_Violation
                 ("unchecked type conversion", N, NIR_Unchecked_Conv);
            else
               Mark (Expression (N));
            end if;

         when N_Validate_Unchecked_Conversion =>
            Mark_Violation ("unchecked conversion", N, NIR_Unchecked_Conv);

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
               T  : constant Entity_Id := Defining_Identifier (N);
               BT : constant Entity_Id := Base_Type (T);
            begin
               Mark_Entity (T);
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
            Mark_Violation ("tasking", N, NIR_Tasking);

         --  The following kinds can be safely ignored by marking

         when N_Character_Literal                      |
              N_Formal_Object_Declaration              |
              N_Formal_Package_Declaration             |
              N_Formal_Subprogram_Declaration          |
              N_Formal_Type_Declaration                |
              N_Freeze_Entity                          |
              N_Function_Instantiation                 |
              N_Generic_Function_Renaming_Declaration  |
              N_Generic_Package_Declaration            |
              N_Generic_Package_Renaming_Declaration   |
              N_Generic_Procedure_Renaming_Declaration |
              N_Generic_Subprogram_Declaration         |
              N_Implicit_Label_Declaration             |
              N_Incomplete_Type_Declaration            |
              N_Integer_Literal                        |
              N_Itype_Reference                        |
              N_Label                                  |
              N_Null_Statement                         |
              N_Operator_Symbol                        |
              N_Others_Choice                          |
              N_Package_Instantiation                  |
              N_Package_Renaming_Declaration           |
              N_Procedure_Instantiation                |
              N_Real_Literal                           |
              N_String_Literal                         |
              N_Subprogram_Info                        |
              N_Subprogram_Renaming_Declaration        |
              N_Use_Package_Clause                     |
              N_With_Clause                            |
              N_Use_Type_Clause                        =>
            null;

         --  Object renamings are rewritten by expansion, but they are kept in
         --  the tree, so just ignore them.

         when N_Object_Renaming_Declaration =>
            null;

         --  The following kinds are rewritten by expansion

         when N_Expression_Function =>
            raise Program_Error;

         --  The following kind is never generated in SPARK mode

         when N_Expression_With_Actions =>
            raise Program_Error;

         --  Mark should not be called on other kinds

         when
              N_Abortable_Part |
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

            if not (Nkind (N) = N_Subtype_Declaration
                     or else
                    Nkind (N) = N_Full_Type_Declaration
                     or else
                    (Nkind (N) = N_Object_Declaration
                      and then Constant_Present (N)))
            then
               return False;
            end if;

            Next (N);
         end loop;

         return True;
      end Acceptable_Actions;

   begin
      if Present (L) then
         Mark_List (L);
         if not Acceptable_Actions (L) then
            Mark_Violation ("expression with action", N, NYI_Expr_With_Action);
         end if;
      end if;
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
      case Attr_Id is
         --  Support special aspects defined in SPARK

         when Attribute_Loop_Entry |

         --  Support a subset of the aspects defined in Ada RM

            Attribute_Ceiling    |
            Attribute_Image      |
            Attribute_First      |
            Attribute_Floor      |
            Attribute_Last       |
            Attribute_Length     |
            Attribute_Max        |
            Attribute_Min        |
            Attribute_Mod        |
            Attribute_Modulus    |
            Attribute_Old        |
            Attribute_Pos        |
            Attribute_Pred       |
            Attribute_Range      |
            Attribute_Result     |
            Attribute_Rounding   |
            Attribute_Truncation |
            Attribute_Succ       |
            Attribute_Val        |
            Attribute_Value      =>

            null;

         when others =>
            Mark_Violation ("attribute", N, NYI_Attribute);
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
      Left_T : constant Entity_Id := Etype (Left_Opnd (N));

   begin
      case N_Binary_Op'(Nkind (N)) is
         when N_Op_Concat =>
            Mark_Violation ("concatenation", N, NYI_Concatenation);

         when N_Op_Lt | N_Op_Le | N_Op_Gt | N_Op_Ge =>
            if Is_Array_Type (Left_T) then
               Mark_Violation
                 ("ordering operator on array type", N, NYI_Array_Operation);
            end if;

         when N_Op_And | N_Op_Or | N_Op_Xor =>
            if Is_Array_Type (Left_T) then
               Mark_Violation
                 ("binary operator on array type", N, NYI_Array_Operation);
            elsif not Is_Boolean_Type (Etype (N)) then
               Mark_Violation
                 ("bitwise modular operation", N, NYI_Arith_Operation);
            end if;

         when N_Op_Shift =>
            Mark_Violation ("operator", N, NYI_Arith_Operation);

         when N_Op_Eq | N_Op_Ne | N_Op_Expon | N_Op_Add | N_Op_Subtract |
              N_Op_Multiply | N_Op_Divide | N_Op_Mod | N_Op_Rem =>
            null;
      end case;

      --  In strict SPARK mode, issue a warning whenever an arithmetic
      --  operation could be reordered by the compiler, like "A + B - C", as a
      --  given ordering may overflow and another may not. Not that a warning
      --  is issued even on operations like "A * B / C" which are not reordered
      --  by GNAT, as they could be reordered according to RM 4.5/13.

      if Opt.SPARK_Strict_Mode

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
      Actuals : constant List_Id := Parameter_Associations (N);

   begin
      if Present (Actuals) then
         Mark_List (Actuals);
      end if;

      --  If this is an indirect call, an entry call, a call to a protected
      --  operation or the subprogram called is not in SPARK, then the call is
      --  not in SPARK.

      if not Is_Entity_Name (Nam)
        or else No (Entity (Nam))
      then
         Mark_Violation ("call", N, NIR_Indirect_Call);

      elsif not In_SPARK (Entity (Nam)) then
         Mark_Violation ("subprogram called", N, From => Entity (Nam));
      end if;
   end Mark_Call;

   ---------------------------
   -- Mark_Compilation_Unit --
   ---------------------------

   procedure Mark_Compilation_Unit (N : Node_Id) is
      CU        : constant Node_Id := Parent (N);
      Context_N : Node_Id;

   begin
      --  Separately mark declarations from Standard as in SPARK or not

      if Defining_Entity (N) = Standard_Standard then
         return;
      end if;

      --  Store scope information

      Get_Scope_Info (N);

      --  Mark entities in SPARK or not

      Push_Entity (Standard_Standard);

      Current_Unit_Is_Main_Body := In_Main_Unit_Body (N);
      Current_Unit_Is_Main_Spec := In_Main_Unit_Spec (N);

      Context_N := First (Context_Items (CU));
      while Present (Context_N) loop
         Mark (Context_N);
         Next (Context_N);
      end loop;

      Mark (N);

      Pop_Entity (Standard_Standard);
   end Mark_Compilation_Unit;

   --------------------------------
   -- Mark_Component_Declaration --
   --------------------------------

   procedure Mark_Component_Declaration (N : Node_Id) is
      Def : constant Node_Id   := Component_Definition (N);

   begin
      if Aliased_Present (Def) then
         Mark_Violation ("ALIASED", N, NIR_Access);
      end if;

      if Present (Access_Definition (Def)) then
         Mark_Violation ("access type", Def, NIR_Access);
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
         Mark_Violation ("handler", First (Handlers), NIR_Exception);
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
                  Mark_Violation ("object", N, From => Entity (N));
               end if;

            when Named_Kind =>
               if not In_SPARK (Entity (N)) then
                  Mark_Violation ("object", N, From => Entity (N));
               end if;

            when Type_Kind =>
               if not In_SPARK (Entity (N)) then
                  Mark_Violation ("type", N, From => Entity (N));
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

            --  We should not encounter abstract state in this traversal

            when E_Abstract_State =>
               raise Program_Error;

            when E_Exception =>
               Mark_Violation ("exception", N, NIR_Exception);

            when E_Entry                 |
                 E_Entry_Family          |
                 E_Entry_Index_Parameter |
                 E_Protected_Object      |
                 E_Protected_Body        |
                 E_Task_Body             =>
               Mark_Violation ("tasking", N, NIR_Tasking);
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
         Mark_Violation ("loop with iterator", N, NYI_Iterators);
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
      Id     : constant Entity_Id := Unique_Defining_Entity (N);
      Decl_N : constant Node_Id   := Parent (Parent (Id));

   begin
      --  Do not analyze generic bodies

      if Ekind (Id) = E_Generic_Package then
         return;
      end if;

      --  Do not analyze bodies for instantiations of the formal containers

      if Is_Instantiation_Of_Formal_Container (Decl_N) then
         return;
      end if;

      Mark_List (Declarations (N));
   end Mark_Package_Body;

   ------------------------------
   -- Mark_Package_Declaration --
   ------------------------------

   procedure Mark_Package_Declaration (N : Node_Id) is

      procedure Declare_In_Container (Decls : List_Id);
      --  Mark types, subprograms and objects from formal container
      --  instantiations.

      --------------------------
      -- Declare_In_Container --
      --------------------------

      procedure Declare_In_Container (Decls : List_Id) is
         Decl : Node_Id;
         Id   : Entity_Id;
      begin
         Decl := First (Decls);

         while Present (Decl) loop
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
                  All_Entities.Include (Id);
                  Entities_In_SPARK.Include (Id);
               end if;
            end if;

            Next (Decl);
         end loop;
      end Declare_In_Container;

      Id         : constant Entity_Id := Defining_Entity (N);
      Vis_Decls  : constant List_Id :=
                     Visible_Declarations (Specification (N));
      Priv_Decls : constant List_Id :=
                     Private_Declarations (Specification (N));

   begin
      --  Do not analyze specs for instantiations of the formal containers.
      --  Only mark types in SPARK or not, and mark all subprograms in SPARK,
      --  but none should be scheduled for translation into Why3.

      if Is_Instantiation_Of_Formal_Container (N) then

         --  Explicitly add the package declaration to the entities to
         --  translate into Why3.

         if Current_Unit_Is_Main_Spec then
            Spec_Entities.Append (Id);

         elsif Current_Unit_Is_Main_Body then
            Body_Entities.Append (Id);
         end if;

         --  Mark types and subprograms from the formal container instantiation
         --  as in SPARK or not.

         Declare_In_Container (Vis_Decls);
         Declare_In_Container (Priv_Decls);

         return;
      end if;

      if Present (Vis_Decls) then
         Mark_List (Vis_Decls);
      end if;

      if Present (Priv_Decls) then
         Mark_List (Priv_Decls);
      end if;
   end Mark_Package_Declaration;

   -----------------
   -- Mark_Pragma --
   -----------------

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

      Error_Msg_Name_1 := Pname;

      case Prag_Id is

         --  pragma Check ([Name    =>] Identifier,
         --                [Check   =>] Boolean_Expression
         --              [,[Message =>] String_Expression]);

         when Pragma_Check =>

            --  Pragma Check generated for Pre/Postconditions are ignored

            if Chars (Get_Pragma_Arg (Arg1)) /= Name_Precondition
              and then Chars (Get_Pragma_Arg (Arg1)) /= Name_Postcondition
            then
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

         --  SPARK pragmas

         when Pragma_Global  |
              Pragma_Depends =>
            null;

         --  Ignored pragmas, either because they are already taken into
         --  account (Precondition and Postcondition), or because they have no
         --  effect on verification (Export, Import, Preelaborate, Pure,
         --  Warnings).

         when Pragma_Export        |
              Pragma_Import        |
              Pragma_Precondition  |
              Pragma_Preelaborate  |
              Pragma_Postcondition |
              Pragma_Pure          |
              Pragma_SPARK_Mode    |
              Pragma_Warnings      =>
            null;

         when Pragma_Overflow_Mode =>
            Error_Msg_F ("?pragma Overflow_Mode in code is ignored", N);

         when others =>
            Mark_Violation ("pragma", N, NYI_Pragma);
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
         All_Entities.Insert (E);
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
      for S in S_Types loop
         All_Entities.Insert (Standard_Entity (S));
         All_Entities.Include (Etype (Standard_Entity (S)));
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
      E   : constant Entity_Id := Unique_Defining_Entity (N);
      HSS : constant Node_Id   := Handled_Statement_Sequence (N);

   begin
      --  Only consider subprogram bodies from the main unit, and not bodies
      --  for expression functions defined in unit specs with'ed directly or
      --  indirectly from the main unit, or bodies from instances of generics
      --  in unit specs with'ed directly or indirectly from the main unit.

      if not (Current_Unit_Is_Main_Spec or Current_Unit_Is_Main_Body)

        --  Ignore bodies defined in the standard library, unless the main unit
        --  is from the standard library. In particular, ignore bodies from
        --  instances of generics defined in the standard library (unless we
        --  are analyzing the standard library itself). As a result, no VC is
        --  generated in this case for standard library code.

        or else
          (Location_In_Standard_Library (Sloc (N))
             and not Unit_In_Standard_Library (Main_Unit))
      then
         return;
      end if;

      --  Content of formal containers is not to be proved

      if Location_In_Formal_Containers (Sloc (E)) then
         return;
      end if;

      --  Do not analyze generic bodies

      if Ekind (E) in Generic_Subprogram_Kind then
         return;
      end if;

      --  Inherit violations from the subprogram spec

      if not In_SPARK (E) then
         Inherit_Violations (Body_Violations, From => E, To => E);
      end if;

      --  If this is a toplevel subprogram, all locally declared entities will
      --  be translated to Why only if the subprogram body is in SPARK.

      if Is_Toplevel_Entity (E) then
         Subprogram_Entities.Clear;
         Push_Toplevel_Subprogram_Body (E);
      end if;

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
         Append_Entity_To_List (Defining_Entity (N));
      end if;

      --  If no violations are attached to E, and it does not have an
      --  applicable pragma SPARK_Mode with value Off, mark its body in
      --  SPARK. For local subprograms inside a toplevel subprogram body,
      --  there is never a violation attached to E, as violations are attached
      --  to the toplevel subprogram entity. If a violation is detected, the
      --  local subprogram will not be added to the entities to translate to
      --  Why.

      if not Has_Body_Violations (E)
        and then not Applicable_SPARK_Pragma_Is (E, SPARK_Off, Is_Body => True)
      then
         Bodies_In_SPARK.Include (E);

         --  For a toplevel subprogram body, if no violations were detected,
         --  move the locally declared entities to either Spec_Entities or
         --  Body_Entities.

         if Is_Toplevel_Entity (E) then
            Append_Subprogram_Entities_To_List;
         end if;
      end if;

      if Is_Toplevel_Entity (E) then
         Pop_Toplevel_Subprogram_Body (E);

         --  Postprocessing: indicate in output file if subprogram is in SPARK
         --  or not, for debug and verifications.

         Generate_Output_In_Out_SPARK (E);
      end if;
   end Mark_Subprogram_Body;

   ---------------------------------
   -- Mark_Subprogram_Declaration --
   ---------------------------------

   procedure Mark_Subprogram_Declaration (N : Node_Id) is
      E : constant Entity_Id := Defining_Entity (N);

   begin
      --  Do not analyze generics

      if Ekind (E) in Generic_Subprogram_Kind then
         return;
      end if;

      --  Mark entity

      Mark_Entity (E);
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
         Mark_Violation ("base type", N, From => T);
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
                           Mark_Violation
                             ("index type", N, From => Entity (Cstr));
                        end if;

                     when N_Subtype_Indication =>
                        if not In_SPARK (Subtype_Mark (Cstr)) then
                           Mark_Violation
                             ("index type", N, From => Subtype_Mark (Cstr));
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
      T : constant Entity_Id := Etype (Right_Opnd (N));

   begin
      case N_Unary_Op'(Nkind (N)) is
         when N_Op_Not =>
            if Is_Array_Type (T) then
               Mark_Violation
                 ("not operator on array type", N, NYI_Arith_Operation);
            end if;

         when N_Op_Abs | N_Op_Plus | N_Op_Minus =>
            null;
      end case;

      Mark (Right_Opnd (N));
   end Mark_Unary_Op;

   ----------------------------------
   -- Most_Underlying_Type_In_SPARK --
   ----------------------------------

   procedure Mark_Most_Underlying_Type_In_SPARK (Id : Entity_Id; N : Node_Id)
   is
      Typ : constant Entity_Id := Most_Underlying_Type (Id);
   begin
      if not In_SPARK (Typ) then
         Mark_Violation ("type", N, From => Typ);
      end if;
   end Mark_Most_Underlying_Type_In_SPARK;

end SPARK_Definition;
