------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--               G N A T 2 W H Y - B O R R O W _ C H E C K E R              --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2017-2019, AdaCore                     --
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

with Atree;                       use Atree;
with Einfo;                       use Einfo;
with Errout;                      use Errout;
with Flow_Types;                  use Flow_Types;
with Flow_Utility;                use Flow_Utility;
with Namet;                       use Namet;
with Nlists;                      use Nlists;
with Sem_Util;                    use Sem_Util;
with Sem_Aux;                     use Sem_Aux;
with Sinfo;                       use Sinfo;
with Snames;                      use Snames;
with SPARK_Annotate;              use SPARK_Annotate;
with SPARK_Definition;            use SPARK_Definition;
with SPARK_Util;                  use SPARK_Util;
with SPARK_Util.Subprograms;      use SPARK_Util.Subprograms;
with SPARK_Util.Types;            use SPARK_Util.Types;
with Treepr;                      use Treepr;

with Ada.Unchecked_Deallocation;
with GNAT.Dynamic_HTables; use GNAT.Dynamic_HTables;

package body Gnat2Why.Borrow_Checker is

   ---------------------------------------------------
   -- Handling of Permissions Associated with Paths --
   ---------------------------------------------------

   package Permissions is
      Elaboration_Context_Max : constant := 1009;
      --  The hash range

      type Elaboration_Context_Index is range 0 .. Elaboration_Context_Max - 1;

      function Elaboration_Context_Hash
        (Key : Entity_Id) return Elaboration_Context_Index;
      --  The hash function

      --  Permission type associated with paths. These are related to but not
      --  the same as the states associated with names used in SPARK RM 3.10:
      --  Unrestricted, Observed, Borrowed, Moved. When ownership rules lead to
      --  a state change for a name, this may correspond to multiple permission
      --  changes for the paths corresponding to the name, its prefixes, and
      --  its extensions. For example, when an object is assigned to, the
      --  corresponding name gets into state Moved, while the path for the name
      --  gets permission Write_Only as well as every prefix of the name, and
      --  every suffix gets permission No_Access.

      type Perm_Kind_Option is
        (None,
         --  Special value used when no permission is passed around

         No_Access,
         --  The path cannot be accessed for reading or writing. This is the
         --  case for the path of a name in the Borrowed state.

         Read_Only,
         --  The path can only be accessed for reading. This is the case for
         --  the path of a name in the Observed state.

         Read_Write,
         --  The path can be accessed for both reading and writing. This is the
         --  case for the path of a name in the Unrestricted state.

         Write_Only
         --  The path can only be accessed for writing. This is the case for
         --  the path of a name in the Moved state.
        );

      subtype Perm_Kind is Perm_Kind_Option range No_Access .. Write_Only;
      subtype Read_Perm is Perm_Kind range Read_Only .. Read_Write;
      subtype Write_Perm is Perm_Kind range Read_Write .. Write_Only;

      type Perm_Tree_Wrapper;

      type Perm_Tree_Access is access Perm_Tree_Wrapper;
      --  A tree of permissions is defined, where the root is a whole object
      --  and tree branches follow access paths in memory. As Perm_Tree is a
      --  discriminated record, a wrapper type is used for the access type
      --  designating a subtree, to make it unconstrained so that it can be
      --  updated.

      --  Nodes in the permission tree are of different kinds

      type Path_Kind is
        (Entire_Object,    --  Scalar object, or folded object of any type
         Reference,        --  Unfolded object of access type
         Array_Component,  --  Unfolded object of array type
         Record_Component  --  Unfolded object of record type
        );

      package Perm_Tree_Maps is new Simple_HTable
        (Header_Num => Elaboration_Context_Index,
         Key        => Entity_Id,
         Element    => Perm_Tree_Access,
         No_Element => null,
         Hash       => Elaboration_Context_Hash,
         Equal      => "=");
      --  The instantation of a hash table, with keys being entities and values
      --  being pointers to permission trees. This is used to define global
      --  environment permissions (entities in that case are stand-alone
      --  objects or formal parameters), as well as the permissions for the
      --  extensions of a Record_Component node (entities in that case are
      --  record components).

      --  The definition of permission trees. This is a tree, which has a
      --  permission at each node, and depending on the type of the node, can
      --  have zero, one, or more children reached through an access to tree.

      type Perm_Tree (Kind : Path_Kind := Entire_Object) is record
         Permission : Perm_Kind;
         --  Permission at this level in the path

         Is_Node_Deep : Boolean;
         --  Whether this node is of a "deep" type, i.e. an access type or a
         --  composite type containing access type subcomponents. This
         --  corresponds to both "observing" and "owning" types in SPARK RM
         --  3.10. To be used when moving the path.

         Explanation : Node_Id;
         --  Node that can be used in an explanation for a permission mismatch

         case Kind is
            --  An entire object is either a leaf (an object which cannot be
            --  extended further in a path) or a subtree in folded form (which
            --  could later be unfolded further in another kind of node). The
            --  field Children_Permission specifies a permission for every
            --  extension of that node if that permission is different from the
            --  node's permission.

            when Entire_Object =>
               Children_Permission : Perm_Kind;

            --  Unfolded path of access type. The permission of the object
            --  pointed to is given in Get_All.

            when Reference =>
               Get_All : Perm_Tree_Access;

            --  Unfolded path of array type. The permission of elements is
            --  given in Get_Elem.

            when Array_Component =>
               Get_Elem : Perm_Tree_Access;

            --  Unfolded path of record type. The permission of the components
            --  is given in Component.

            when Record_Component =>
               Component : Perm_Tree_Maps.Instance;
         end case;
      end record;

      type Perm_Tree_Wrapper is record
         Tree : Perm_Tree;
      end record;
      --  We use this wrapper in order to have unconstrained discriminants

      type Perm_Env is new Perm_Tree_Maps.Instance;
      --  The definition of a permission environment for the analysis. This is
      --  just a hash table from entities to permission trees.

      type Perm_Env_Access is access Perm_Env;
      --  Access to permission environments

      package Env_Maps is new Simple_HTable
        (Header_Num => Elaboration_Context_Index,
         Key        => Entity_Id,
         Element    => Perm_Env_Access,
         No_Element => null,
         Hash       => Elaboration_Context_Hash,
         Equal      => "=");
      --  The instantiation of a hash table whose elements are permission
      --  environments. This hash table is used to save the environments at
      --  the entry of each loop, with the key being the loop label.

      type Env_Backups is new Env_Maps.Instance;
      --  The type defining the hash table saving the environments at the entry
      --  of each loop.

      package Variable_Maps is new Simple_HTable
        (Header_Num => Elaboration_Context_Index,
         Key        => Entity_Id,
         Element    => Node_Id,
         No_Element => Empty,
         Hash       => Elaboration_Context_Hash,
         Equal      => "=");

      type Variable_Mapping is new Variable_Maps.Instance;
      --  Mapping from variables to nodes denoting paths that are observed or
      --  borrowed by the variable.

      --------------------
      -- Simple Getters --
      --------------------

      --  Simple getters to avoid having .all.Tree.Field everywhere. Of course,
      --  that's only for the top access, as otherwise this reverses the order
      --  in accesses visually.

      function Children_Permission (T : Perm_Tree_Access) return Perm_Kind;
      function Component (T : Perm_Tree_Access) return Perm_Tree_Maps.Instance;
      function Explanation (T : Perm_Tree_Access) return Node_Id;
      function Get_All (T : Perm_Tree_Access) return Perm_Tree_Access;
      function Get_Elem (T : Perm_Tree_Access) return Perm_Tree_Access;
      function Is_Node_Deep (T : Perm_Tree_Access) return Boolean;
      function Kind (T : Perm_Tree_Access) return Path_Kind;
      function Permission (T : Perm_Tree_Access) return Perm_Kind;

      -----------------------
      -- Memory Management --
      -----------------------

      procedure Copy_Env
        (From : Perm_Env;
         To   : in out Perm_Env);
      --  Procedure to copy a permission environment

      procedure Move_Env (From, To : in out Perm_Env);
      --  Procedure to move a permission environment. It frees To, moves From
      --  in To and sets From to Nil.

      procedure Move_Variable_Mapping (From, To : in out Variable_Mapping);
      --  Move a variable mapping, freeing memory as needed and resetting the
      --  source mapping.

      procedure Copy_Tree (From, To : Perm_Tree_Access);
      --  Procedure to copy a permission tree

      procedure Free_Env (PE : in out Perm_Env);
      --  Procedure to free a permission environment

      procedure Free_Tree (PT : in out Perm_Tree_Access);
      --  Procedure to free a permission tree

      --------------------
      -- Error Messages --
      --------------------

      procedure Perm_Mismatch
        (N              : Node_Id;
         Exp_Perm       : Perm_Kind;
         Act_Perm       : Perm_Kind;
         Expl           : Node_Id;
         Forbidden_Perm : Boolean := False);
      --  Issues a continuation error message about a mismatch between a
      --  desired permission Exp_Perm and a permission obtained Act_Perm. N
      --  is the node on which the error is reported.

   end Permissions;

   package body Permissions is

      -------------------------
      -- Children_Permission --
      -------------------------

      function Children_Permission (T : Perm_Tree_Access) return Perm_Kind is
      begin
         return T.all.Tree.Children_Permission;
      end Children_Permission;

      ---------------
      -- Component --
      ---------------

      function Component (T : Perm_Tree_Access) return Perm_Tree_Maps.Instance
      is
      begin
         return T.all.Tree.Component;
      end Component;

      --------------
      -- Copy_Env --
      --------------

      procedure Copy_Env (From : Perm_Env; To : in out Perm_Env) is
         Comp_From : Perm_Tree_Access;
         Key_From  : Perm_Tree_Maps.Key_Option;
         Son       : Perm_Tree_Access;

      begin
         Free_Env (To);
         Key_From := Get_First_Key (From);
         while Key_From.Present loop
            Comp_From := Get (From, Key_From.K);
            pragma Assert (Comp_From /= null);

            Son := new Perm_Tree_Wrapper;
            Copy_Tree (Comp_From, Son);

            Set (To, Key_From.K, Son);
            Key_From := Get_Next_Key (From);
         end loop;
      end Copy_Env;

      ---------------
      -- Copy_Tree --
      ---------------

      procedure Copy_Tree (From, To : Perm_Tree_Access) is
      begin
         --  Copy the direct components of the tree

         To.all := From.all;

         --  Now reallocate access components for a deep copy of the tree

         case Kind (From) is
            when Entire_Object =>
               null;

            when Reference =>
               To.all.Tree.Get_All := new Perm_Tree_Wrapper;
               Copy_Tree (Get_All (From), Get_All (To));

            when Array_Component =>
               To.all.Tree.Get_Elem := new Perm_Tree_Wrapper;
               Copy_Tree (Get_Elem (From), Get_Elem (To));

            when Record_Component =>
               declare
                  Comp_From : Perm_Tree_Access;
                  Key_From : Perm_Tree_Maps.Key_Option;
                  Son : Perm_Tree_Access;
                  Hash_Table : Perm_Tree_Maps.Instance;
               begin
                  --  We put a new hash table, so that it gets dealiased from
                  --  the Component (From) hash table.
                  To.all.Tree.Component := Hash_Table;
                  Key_From := Perm_Tree_Maps.Get_First_Key
                    (Component (From));

                  while Key_From.Present loop
                     Comp_From := Perm_Tree_Maps.Get
                       (Component (From), Key_From.K);
                     pragma Assert (Comp_From /= null);
                     Son := new Perm_Tree_Wrapper;
                     Copy_Tree (Comp_From, Son);
                     Perm_Tree_Maps.Set
                       (To.all.Tree.Component, Key_From.K, Son);
                     Key_From := Perm_Tree_Maps.Get_Next_Key
                       (Component (From));
                  end loop;
               end;
         end case;
      end Copy_Tree;

      ------------------------------
      -- Elaboration_Context_Hash --
      ------------------------------

      function Elaboration_Context_Hash
        (Key : Entity_Id) return Elaboration_Context_Index
      is
      begin
         return Elaboration_Context_Index (Key mod Elaboration_Context_Max);
      end Elaboration_Context_Hash;

      --------------
      -- Free_Env --
      --------------

      procedure Free_Env (PE : in out Perm_Env) is
         CompO : Perm_Tree_Access;
      begin
         CompO := Get_First (PE);
         while CompO /= null loop
            Free_Tree (CompO);
            CompO := Get_Next (PE);
         end loop;

         Reset (PE);
      end Free_Env;

      ---------------
      -- Free_Tree --
      ---------------

      procedure Free_Tree (PT : in out Perm_Tree_Access) is
         procedure Free_Perm_Tree_Dealloc is
           new Ada.Unchecked_Deallocation
             (Perm_Tree_Wrapper, Perm_Tree_Access);
         --  The deallocator for permission_trees

      begin
         case Kind (PT) is
            when Entire_Object =>
               null;

            when Reference =>
               Free_Tree (PT.all.Tree.Get_All);

            when Array_Component =>
               Free_Tree (PT.all.Tree.Get_Elem);

            when Record_Component =>
               declare
                  Comp : Perm_Tree_Access;

               begin
                  Comp := Perm_Tree_Maps.Get_First (Component (PT));
                  while Comp /= null loop

                     --  Free every Component subtree

                     Free_Tree (Comp);
                     Comp := Perm_Tree_Maps.Get_Next (Component (PT));
                  end loop;
               end;
         end case;

         Free_Perm_Tree_Dealloc (PT);
      end Free_Tree;

      -----------------
      -- Explanation --
      -----------------

      function Explanation (T : Perm_Tree_Access) return Node_Id is
      begin
         return T.all.Tree.Explanation;
      end Explanation;

      -------------
      -- Get_All --
      -------------

      function Get_All (T : Perm_Tree_Access) return Perm_Tree_Access is
      begin
         return T.all.Tree.Get_All;
      end Get_All;

      --------------
      -- Get_Elem --
      --------------

      function Get_Elem (T : Perm_Tree_Access) return Perm_Tree_Access is
      begin
         return T.all.Tree.Get_Elem;
      end Get_Elem;

      ------------------
      -- Is_Node_Deep --
      ------------------

      function Is_Node_Deep (T : Perm_Tree_Access) return Boolean is
      begin
         return T.all.Tree.Is_Node_Deep;
      end Is_Node_Deep;

      ----------
      -- Kind --
      ----------

      function Kind (T : Perm_Tree_Access) return Path_Kind is
      begin
         return T.all.Tree.Kind;
      end Kind;

      --------------
      -- Move_Env --
      --------------

      procedure Move_Env (From, To : in out Perm_Env) is
      begin
         Free_Env (To);
         To   := From;
         From := Perm_Env (Perm_Tree_Maps.Nil);
      end Move_Env;

      ---------------------------
      -- Move_Variable_Mapping --
      ---------------------------

      procedure Move_Variable_Mapping (From, To : in out Variable_Mapping) is
      begin
         Reset (To);
         To   := From;
         From := Variable_Mapping (Variable_Maps.Nil);
      end Move_Variable_Mapping;

      ----------------
      -- Permission --
      ----------------

      function Permission (T : Perm_Tree_Access) return Perm_Kind is
      begin
         return T.all.Tree.Permission;
      end Permission;

      -------------------
      -- Perm_Mismatch --
      -------------------

      procedure Perm_Mismatch
        (N              : Node_Id;
         Exp_Perm       : Perm_Kind;
         Act_Perm       : Perm_Kind;
         Expl           : Node_Id;
         Forbidden_Perm : Boolean := False)
      is
      begin
         Error_Msg_Sloc := Sloc (Expl);

         if Forbidden_Perm then
            if Exp_Perm = No_Access then
               Error_Msg_N ("\object was moved #", N);
            else
               raise Program_Error;
            end if;
         else
            case Exp_Perm is
               when Write_Perm =>
                  if Act_Perm = Read_Only then
                     Error_Msg_N
                       ("\object was declared as not writeable #", N);
                  else
                     Error_Msg_N ("\object was moved #", N);
                  end if;

               when Read_Only =>
                  Error_Msg_N ("\object was moved #", N);

               when No_Access =>
                  raise Program_Error;
            end case;
         end if;
      end Perm_Mismatch;

   end Permissions;

   use Permissions;

   --------------------------------------
   -- Analysis modes for AST traversal --
   --------------------------------------

   --  The different modes for analysis. This allows checking whether a path
   --  has the right permission, and also updating permissions when a path is
   --  moved, borrowed, or observed.

   type Extended_Checking_Mode is

     (Read_Subexpr,
      --  Special value used for assignment, to check that subexpressions of
      --  the assigned path are readable.

      Read,
      --  Default mode

      Move,
      --  Move semantics. Checks that paths have Read_Write permission. After
      --  moving a path, its permission and the permission of its prefixes are
      --  set to Write_Only, while the permission of its extensions is set to
      --  No_Access.

      Assign,
      --  Used for the target of an assignment, or an actual parameter with
      --  mode OUT. Checks that paths have Write_Perm permission. After
      --  assigning to a path, its permission and the permission of its
      --  extensions are set to Read_Write. The permission of its prefixes may
      --  be normalized from Write_Only to Read_Write depending on other
      --  permissions in the tree (a prefix gets permission Read_Write when all
      --  its extensions become Read_Write).

      Borrow,
      --  Borrow semantics. Checks that paths have Read_Write permission. After
      --  borrowing a path, its permission and the permission of its prefixes
      --  and extensions are set to No_Access.

      Observe
      --  Observe semantics. Checks that paths have Read_Perm permission. After
      --  observing a path, its permission and the permission of its prefixes
      --  and extensions are set to Read_Only.
     );

   subtype Checking_Mode is Extended_Checking_Mode range Read .. Observe;

   type Result_Kind is (Folded, Unfolded);
   --  The type declaration to discriminate in the Perm_Or_Tree type

   --  The result type of the function Get_Perm_Or_Tree. This returns either a
   --  tree when it found the appropriate tree, or a permission when the search
   --  finds a leaf and the subtree we are looking for is folded. In the last
   --  case, we return instead the Children_Permission field of the leaf.

   type Perm_Or_Tree (R : Result_Kind) is record
      case R is
         when Folded   =>
            Found_Permission : Perm_Kind;
            Explanation      : Node_Id;
         when Unfolded =>
            Tree_Access      : Perm_Tree_Access;
      end case;
   end record;

   type Expr_Or_Ent (Is_Ent : Boolean) is record
      case Is_Ent is
         when False =>
            Expr : Node_Id;
         when True  =>
            Ent  : Entity_Id;
            Loc  : Node_Id;
      end case;
   end record;

   -----------------------
   -- Local subprograms --
   -----------------------

   function "+" (X : Node_Id) return Expr_Or_Ent is
      ((Is_Ent => False, Expr => X));

   function "<=" (P1, P2 : Perm_Kind) return Boolean;
   function ">=" (P1, P2 : Perm_Kind) return Boolean;
   function Glb  (P1, P2 : Perm_Kind) return Perm_Kind;
   function Lub  (P1, P2 : Perm_Kind) return Perm_Kind;

   procedure Check_Assignment (Target : Node_Or_Entity_Id; Expr : Node_Id);
   --  Handle assignment as part of an assignment statement or an object
   --  declaration.

   procedure Check_Call_Statement (Call : Node_Id);

   procedure Check_Callable_Body (Id : Entity_Id);
   --  Entry point for the analysis of a subprogram or entry body

   procedure Check_Declaration (Decl : Node_Id);

   procedure Check_Expression (Expr : Node_Id; Mode : Extended_Checking_Mode);
   pragma Precondition (Nkind_In (Expr, N_Index_Or_Discriminant_Constraint,
                                        N_Range_Constraint,
                                        N_Subtype_Indication,
                                        N_Digits_Constraint,
                                        N_Delta_Constraint)
                        or else Nkind (Expr) in N_Subexpr);

   procedure Check_Expr_Or_Ent
     (Expr : Expr_Or_Ent;
      Mode : Extended_Checking_Mode)
     with Pre =>
       (Expr.Is_Ent or else
          Nkind (Expr.Expr) in N_Index_Or_Discriminant_Constraint
                             | N_Range_Constraint
                             | N_Subtype_Indication
                             | N_Digits_Constraint
                             | N_Delta_Constraint
                             | N_Subexpr);

   procedure Check_Globals (Subp : Entity_Id; Loc : Node_Id);
   --  This procedure takes a subprogram called and checks the permission of
   --  globals.

   --  Checking proceduress for safe pointer usage. These procedures traverse
   --  the AST, check nodes for correct permissions according to SPARK RM 3.10,
   --  and update permissions depending on the node kind. The main procedure
   --  Check_Node is mutually recursive with the specialized procedures that
   --  follow.

   procedure Check_List (L : List_Id);
   --  Calls Check_Node on each element of the list

   procedure Check_Loop_Statement (Stmt : Node_Id);

   procedure Check_Node (N : Node_Id);
   --  Main traversal procedure to check safe pointer usage

   procedure Check_Not_Borrowed (Expr : Expr_Or_Ent; Root : Entity_Id);
   --  Check expression Expr originating in Root was not borrowed

   procedure Check_Not_Observed (Expr : Expr_Or_Ent; Root : Entity_Id);
   --  Check expression Expr originating in Root was not observed

   procedure Check_Package_Spec (Id : Entity_Id);
   --  Check the package visible and private declarations in the current
   --  context. Update the context accordingly.

   procedure Check_Package_Body (Id : Entity_Id);
   --  Check the package body in the current context. Reset the context
   --  afterwards.

   procedure Check_Package_Entity (Id : Entity_Id);
   --  Check both the package declaration and its body in a fresh context.
   --  Reset the context afterwards.

   procedure Check_Parameter_Or_Global
     (Expr       : Expr_Or_Ent;
      Typ        : Entity_Id;
      Kind       : Formal_Kind;
      Subp       : Entity_Id;
      Global_Var : Boolean);
   --  Check the permission of every actual parameter or global

   procedure Check_Pragma (Prag : Node_Id);

   procedure Check_Statement (Stmt : Node_Id);

   function Get_Expl (N : Expr_Or_Ent) return Node_Id;
   --  The function that takes a name as input and returns an explanation node
   --  for the permission associated with it.

   function Get_Perm (N : Expr_Or_Ent) return Perm_Kind;
   --  The function that takes a name as input and returns a permission
   --  associated with it.

   function Get_Perm_Or_Tree (N : Expr_Or_Ent) return Perm_Or_Tree;
   pragma Precondition (N.Is_Ent or else Is_Path_Expression (N.Expr));
   --  This function gets a node and looks recursively to find the appropriate
   --  subtree for that node. If the tree is folded on that node, then it
   --  returns the permission given at the right level.

   function Get_Perm_Tree (N : Expr_Or_Ent) return Perm_Tree_Access;
   pragma Precondition (N.Is_Ent or else Is_Path_Expression (N.Expr));
   --  This function gets a node and looks recursively to find the appropriate
   --  subtree for that node. If the tree is folded, then it unrolls the tree
   --  up to the appropriate level.

   generic
      with procedure Handle_Parameter_Or_Global
        (Expr       : Expr_Or_Ent;
         Formal_Typ : Entity_Id;
         Param_Mode : Formal_Kind;
         Subp       : Entity_Id;
         Global_Var : Boolean);
   procedure Handle_Globals (Subp : Entity_Id; Loc : Node_Id);
   --  Handling of globals is factored in a generic instantiated below

   function Has_Array_Component (Expr : Node_Id) return Boolean;
   pragma Precondition (Is_Path_Expression (Expr));
   --  This function gets a node and looks recursively to determine whether the
   --  given path has any array component.

   procedure Hp (P : Perm_Env);
   --  A procedure that outputs the hash table. This function is used only in
   --  the debugger to look into a hash table.
   pragma Unreferenced (Hp);

   function Is_Prefix_Or_Almost
     (Pref : Node_Id;
      Expr : Expr_Or_Ent) return Boolean;
   --  Determine if the candidate Prefix is indeed a prefix of Expr, or almost
   --  a prefix, in the sense that they could still refer to overlapping memory
   --  locations.

   function Is_Read_Only (E : Entity_Id) return Boolean with
     Pre => Is_Object (E);
   --  Return True if E is declared as Read_Only (ie. a constant which is not
   --  of access-to-variable type, or a variable of access-to-constant type).

   function Loop_Of_Exit (N : Node_Id) return Entity_Id;
   --  A function that takes an exit statement node and returns the entity of
   --  the loop that this statement is exiting from.

   procedure Merge_Env (Source : in out Perm_Env; Target : in out Perm_Env);
   --  Merge Target and Source into Target, and then deallocate the Source

   procedure Perm_Error
     (N              : Expr_Or_Ent;
      Perm           : Perm_Kind;
      Found_Perm     : Perm_Kind;
      Expl           : Node_Id;
      Forbidden_Perm : Boolean := False);
   --  A procedure that is called when the permissions found contradict the
   --  rules established by the RM. This function is called with the node and
   --  the permission that was expected, and issues an error message with the
   --  appropriate values.

   procedure Perm_Error_Subprogram_End
     (E          : Entity_Id;
      Subp       : Entity_Id;
      Perm       : Perm_Kind;
      Found_Perm : Perm_Kind;
      Expl       : Node_Id);
   --  A procedure that is called when the permissions found contradict the
   --  rules established by the RM at the end of subprograms. This function is
   --  called with the node, the node of the returning function, and the
   --  permission that was expected, and adds an error message with the
   --  appropriate values.

   procedure Process_Path (Expr : Expr_Or_Ent; Mode : Checking_Mode);
   pragma Precondition (Expr.Is_Ent or else Is_Path_Expression (Expr.Expr));
   --  Check correct permission for the path in the checking mode Mode, and
   --  update permissions of the path and its prefixes/extensions.

   procedure Return_Globals (Subp : Entity_Id);
   --  Takes a subprogram as input, and checks that all borrowed global items
   --  of the subprogram indeed have Read_Write permission at the end of the
   --  subprogram execution.

   procedure Return_Parameter_Or_Global
     (Id         : Entity_Id;
      Typ        : Entity_Id;
      Kind       : Formal_Kind;
      Subp       : Entity_Id;
      Global_Var : Boolean);
   --  Auxiliary procedure to Return_Parameters and Return_Globals

   procedure Return_Parameters (Subp : Entity_Id);
   --  Takes a subprogram as input, and checks that all out parameters of the
   --  subprogram indeed have Read_Write permission at the end of the
   --  subprogram execution.

   procedure Set_Perm_Extensions
     (T    : Perm_Tree_Access;
      P    : Perm_Kind;
      Expl : Node_Id);
   --  This procedure takes an access to a permission tree and modifies the
   --  tree so that any strict extensions of the given tree become of the
   --  access specified by parameter P.

   procedure Set_Perm_Extensions_Move
     (T    : Perm_Tree_Access;
      E    : Entity_Id;
      Expl : Node_Id);
   --  Set permissions to
   --    No for any extension with more .all
   --    W for any deep extension with same number of .all
   --    RW for any shallow extension with same number of .all

   function Set_Perm_Prefixes
     (N    : Expr_Or_Ent;
      Perm : Perm_Kind_Option;
      Expl : Node_Id) return Perm_Tree_Access;
   pragma Precondition (N.Is_Ent or else Is_Path_Expression (N.Expr));
   --  This function modifies the permissions of a given node in the permission
   --  environment as well as all the prefixes of the path, to the new
   --  permission Perm. The general rule here is that everybody updates the
   --  permission of the subtree they are returning.

   procedure Set_Perm_Prefixes_Assign (N : Expr_Or_Ent);
   pragma Precondition (N.Is_Ent or else Is_Path_Expression (N.Expr));
   --  This procedure takes a name as an input and sets in the permission
   --  tree the given permission to the given name. The general rule here is
   --  that everybody updates the permission of the subtree it is returning.
   --  The permission of the assigned path has been set to RW by the caller.
   --
   --  Case where we have to normalize a tree after the correct permissions
   --  have been assigned already. We look for the right subtree at the given
   --  path, actualize its permissions, and then call the normalization on its
   --  parent.
   --
   --  Example: We assign x.y and x.z, and then Set_Perm_Prefixes_Assign will
   --  change the permission of x to RW because all of its components have
   --  permission RW.

   procedure Setup_Globals (Subp : Entity_Id);
   --  Takes a subprogram as input, and sets up the environment by adding
   --  global items with appropriate permissions.

   procedure Setup_Parameter_Or_Global
     (Id         : Entity_Id;
      Typ        : Entity_Id;
      Kind       : Formal_Kind;
      Subp       : Entity_Id;
      Global_Var : Boolean;
      Expl       : Node_Id);
   --  Auxiliary procedure to Setup_Parameters and Setup_Globals

   procedure Setup_Parameters (Subp : Entity_Id);
   --  Takes a subprogram as input, and sets up the environment by adding
   --  formal parameters with appropriate permissions.

   procedure Setup_Protected_Components (Subp : Entity_Id);
   --  Takes a protected operation as input, and sets up the environment by
   --  adding protected components with appropriate permissions.

   ----------------------
   -- Global Variables --
   ----------------------

   Current_Perm_Env : Perm_Env;
   --  The permission environment that is used for the analysis. This
   --  environment can be saved, modified, reinitialized, but should be the
   --  only one valid from which to extract the permissions of the paths in
   --  scope. The analysis ensures at each point that this variables contains
   --  a valid permission environment with all bindings in scope.

   Inside_Procedure_Call : Boolean := False;
   --  Set while checking the actual parameters of a procedure or entry call

   Inside_Elaboration : Boolean := False;
   --  Set during package spec/body elaboration, during which move and local
   --  observe/borrow are not allowed. As a result, no other checking is needed
   --  during elaboration.

   Current_Loops_Envs : Env_Backups;
   --  This variable contains saves of permission environments at each loop the
   --  analysis entered. Each saved environment can be reached with the label
   --  of the loop.

   Current_Loops_Accumulators : Env_Backups;
   --  This variable contains the environments used as accumulators for loops,
   --  that consist of the merge of all environments at each exit point of
   --  the loop (which can also be the entry point of the loop in the case of
   --  non-infinite loops), each of them reachable from the label of the loop.
   --  We require that the environment stored in the accumulator be less
   --  restrictive than the saved environment at the beginning of the loop, and
   --  the permission environment after the loop is equal to the accumulator.

   Current_Borrowers : Variable_Mapping;
   --  Mapping from borrowers to the path borrowed

   Current_Observers : Variable_Mapping;
   --  Mapping from observers to the path observed

   Permission_Error : Boolean := False;
   --  Should be set to true when an error message is emitted

   --------------------
   -- Handle_Globals --
   --------------------

   procedure Handle_Globals (Subp : Entity_Id; Loc : Node_Id) is

      --  Local subprograms

      procedure Handle_Global (E : Entity_Id; Kind : Formal_Kind);
      --  Call Handle_Parameter_Or_Global on E

      -------------------
      -- Handle_Global --
      -------------------

      procedure Handle_Global (E : Entity_Id; Kind : Formal_Kind) is
      begin
         Handle_Parameter_Or_Global
           (Expr       => Expr_Or_Ent'
              (Is_Ent => True,
               Ent    => E,
               Loc    => Loc),
            Formal_Typ => Etype (E),
            Param_Mode => Kind,
            Subp       => Subp,
            Global_Var => True);
      end Handle_Global;

      procedure Process_All is new Process_Referenced_Entities (Handle_Global);

   --  Start of processing for Handle_Globals

   begin
      Process_All (Subp);
   end Handle_Globals;

   ----------
   -- "<=" --
   ----------

   function "<=" (P1, P2 : Perm_Kind) return Boolean is
   begin
      return P2 >= P1;
   end "<=";

   ----------
   -- ">=" --
   ----------

   function ">=" (P1, P2 : Perm_Kind) return Boolean is
   begin
      case P2 is
         when No_Access  => return True;
         when Read_Only  => return P1 in Read_Perm;
         when Write_Only => return P1 in Write_Perm;
         when Read_Write => return P1 = Read_Write;
      end case;
   end ">=";

   ----------------------
   -- Check_Assignment --
   ----------------------

   procedure Check_Assignment (Target : Node_Or_Entity_Id; Expr : Node_Id) is
      Is_Decl : constant Boolean := Nkind (Target) = N_Defining_Identifier;

      --  Local subprograms

      procedure Handle_Borrow
        (Var  : Entity_Id;
         Expr : Node_Id);
      --  Update map of current borrowers

      procedure Handle_Observe
        (Var  : Entity_Id;
         Expr : Node_Id);
      --  Update map of current observers

      -------------------
      -- Handle_Borrow --
      -------------------

      procedure Handle_Borrow
        (Var  : Entity_Id;
         Expr : Node_Id)
      is
         Borrowed : constant Node_Id := Get_Observed_Or_Borrowed_Expr (Expr);
      begin
         if Is_Decl then
            Set (Current_Borrowers, Var, Borrowed);
         else
            pragma Assert (Get_Root_Object (Borrowed) = Var);
         end if;
      end Handle_Borrow;

      --------------------
      -- Handle_Observe --
      --------------------

      procedure Handle_Observe
        (Var  : Entity_Id;
         Expr : Node_Id)
      is
         Observed : constant Node_Id := Get_Observed_Or_Borrowed_Expr (Expr);
      begin
         if Is_Decl then
            Set (Current_Observers, Var, Observed);
         else
            pragma Assert (Get_Root_Object (Observed) = Var);
         end if;
      end Handle_Observe;

      --  Local variables

      Target_Typ  : constant Node_Id := Etype (Target);
      Target_Root : Entity_Id;
      Expr_Root   : Entity_Id;
      Perm        : Perm_Kind;
      Dummy       : Boolean := True;

   --  Start of processing for Check_Assignment

   begin
      if Is_Anonymous_Access_Type (Target_Typ) then
         if Is_Decl then
            Target_Root := Target;
         else
            Target_Root := Get_Root_Object (Target);
         end if;

         Expr_Root := Get_Root_Object (Expr);

         --  SPARK RM 3.10(7): For an assignment statement where the target is
         --  a stand-alone object of an anonymous access-to-object type.

         pragma Assert (Present (Target_Root));

         --  If the type of the target is an anonymous access-to-constant type
         --  (an observing access type), the source shall be an owning access
         --  object denoted by a name that is not in the Moved state, and whose
         --  root object is not in the Moved state and is not declared at a
         --  statically deeper accessibility level than that of the target
         --  object.

         if Is_Access_Constant (Target_Typ) then
            declare
               E_Root : constant Expr_Or_Ent :=
                 (Is_Ent => True, Ent => Expr_Root, Loc => Expr);
            begin
               Perm := Get_Perm (+Expr);

               if Perm = No_Access then
                  Perm_Error (+Expr, No_Access, No_Access,
                              Expl => Get_Expl (+Expr),
                              Forbidden_Perm => True);
                  return;
               end if;

               Perm := Get_Perm (E_Root);

               if Perm = No_Access then
                  Perm_Error (+Expr, No_Access, No_Access,
                              Expl => Get_Expl (E_Root),
                              Forbidden_Perm => True);
                  return;
               end if;
            end;

            --  ??? check accessibility level

            Check_Expression (Expr, Observe);
            Handle_Observe (Target_Root, Expr);

         --  If the type of the target is an anonymous access-to-variable
         --  type (an owning access type), the source shall be an owning
         --  access object denoted by a name that is in the Unrestricted
         --  state, and whose root object is the target object itself.

         else
            Perm := Get_Perm (+Expr);

            if Perm /= Read_Write then
               Perm_Error (+Expr, Read_Write, Perm,
                           Expl => Get_Expl (+Expr));
               return;
            end if;

            pragma Assert
              (if not Is_Decl
               then Is_Entity_Name (Target) and then Target_Root = Expr_Root);

            Check_Expression (Expr, Borrow);
            Handle_Borrow (Target_Root, Expr);
         end if;

      elsif Is_Deep (Target_Typ) then

         --  Expression not allowed as source of move

         pragma Assert (Is_Path_Expression (Expr));
         Check_Expression (Expr, Move);

      else
         Check_Expression (Expr, Read);
      end if;
   end Check_Assignment;

   --------------------------
   -- Check_Call_Statement --
   --------------------------

   procedure Check_Call_Statement (Call : Node_Id) is

      Subp : constant Entity_Id := Get_Called_Entity (Call);

      --  Local subprograms

      procedure Check_Param (Formal : Entity_Id; Actual : Node_Id);
      --  Check the permission of every actual parameter

      procedure Update_Param (Formal : Entity_Id; Actual : Node_Id);
      --  Update the permission of OUT actual parameters

      -----------------
      -- Check_Param --
      -----------------

      procedure Check_Param (Formal : Entity_Id; Actual : Node_Id) is
      begin
         Check_Parameter_Or_Global
           (Expr       => +Actual,
            Typ        => Etype (Formal),
            Kind       => Ekind (Formal),
            Subp       => Subp,
            Global_Var => False);
      end Check_Param;

      ------------------
      -- Update_Param --
      ------------------

      procedure Update_Param (Formal : Entity_Id; Actual : Node_Id) is
         Mode : constant Entity_Kind := Ekind (Formal);

      begin
         case Formal_Kind'(Mode) is
            when E_Out_Parameter =>
               Check_Expression (Actual, Assign);

            when others =>
               null;
         end case;
      end Update_Param;

      procedure Check_Params is new
        Iterate_Call_Parameters (Check_Param);

      procedure Update_Params is new
        Iterate_Call_Parameters (Update_Param);

   --  Start of processing for Check_Call_Statement

   begin
      Inside_Procedure_Call := True;
      Check_Params (Call);
      if Ekind (Get_Called_Entity (Call)) = E_Subprogram_Type then
         raise Program_Error;
      else
         Check_Globals (Get_Called_Entity (Call), Call);
      end if;

      Inside_Procedure_Call := False;
      Update_Params (Call);
   end Check_Call_Statement;

   -------------------------
   -- Check_Callable_Body --
   -------------------------

   procedure Check_Callable_Body (Id : Entity_Id) is
      Save_In_Elab    : constant Boolean := Inside_Elaboration;
      Body_N          : constant Node_Id := Get_Body (Id);

      Saved_Env       : Perm_Env;
      Saved_Borrowers : Variable_Mapping;
      Saved_Observers : Variable_Mapping;

   begin
      Inside_Elaboration := False;

      --  Save environment and put a new one in place

      Move_Env (Current_Perm_Env, Saved_Env);
      Move_Variable_Mapping (Current_Borrowers, Saved_Borrowers);
      Move_Variable_Mapping (Current_Observers, Saved_Observers);

      --  Add formals and globals to the environment with adequate permissions

      if Is_Subprogram_Or_Entry (Id) then
         Setup_Parameters (Id);
         Setup_Globals (Id);
      end if;

      --  For protected operations, add protected components to the environment
      --  with adequate permissions.

      if Is_Protected_Operation (Id) then
         Setup_Protected_Components (Id);
      end if;

      --  Analyze the body of the subprogram

      Check_List (Declarations (Body_N));

      if Ekind (Id) in Subprogram_Kind | Entry_Kind | Task_Kind then
         Check_Node (Handled_Statement_Sequence (Body_N));
      end if;

      --  Check the read-write permissions of borrowed parameters/globals

      if Ekind_In (Id, E_Procedure, E_Entry)
        and then not No_Return (Id)
      then
         Return_Parameters (Id);
         Return_Globals (Id);
      end if;

      --  Restore the saved environment and free the current one

      Move_Env (Saved_Env, Current_Perm_Env);
      Move_Variable_Mapping (Saved_Borrowers, Current_Borrowers);
      Move_Variable_Mapping (Saved_Observers, Current_Observers);

      Inside_Elaboration := Save_In_Elab;
   end Check_Callable_Body;

   -----------------------
   -- Check_Declaration --
   -----------------------

   procedure Check_Declaration (Decl : Node_Id) is
      Target     : constant Entity_Id := Defining_Identifier (Decl);
      Target_Typ : constant Node_Id := Etype (Target);
      Expr       : Node_Id;

   begin
      --  Check permission-related legality rules

      case N_Declaration'(Nkind (Decl)) is
         when N_Full_Type_Declaration =>
            null;

         --  ??? What about component declarations with defaults.

         when N_Subtype_Declaration =>
            Check_Expression (Subtype_Indication (Decl), Read);

         when N_Object_Declaration =>
            Expr := Expression (Decl);

            if Present (Expr) then
               Check_Assignment (Target => Target,
                                 Expr   => Expr);
            end if;

            --  Always add variable to the current permission environment,
            --  even in the illegal case, as the rest of the analysis expects
            --  to find it.

            if Is_Deep (Target_Typ) then
               declare
                  Perm : constant Perm_Kind :=
                    (if Is_Read_Only (Target) then Read_Only else Read_Write);
                  Tree : constant Perm_Tree_Access :=
                    new Perm_Tree_Wrapper'
                      (Tree =>
                         (Kind                => Entire_Object,
                          Is_Node_Deep        => True,
                          Explanation         => Decl,
                          Permission          => Perm,
                          Children_Permission => Perm));
               begin
                  Set (Current_Perm_Env, Target, Tree);
               end;
            end if;

         when N_Iterator_Specification =>
            null;

         when N_Loop_Parameter_Specification =>
            null;

         --  Checking should not be called directly on these nodes

         when N_Function_Specification
            | N_Entry_Declaration
            | N_Procedure_Specification
            | N_Component_Declaration
         =>
            raise Program_Error;

         --  Ignored constructs for pointer checking

         when N_Formal_Object_Declaration
            | N_Formal_Type_Declaration
            | N_Incomplete_Type_Declaration
            | N_Private_Extension_Declaration
            | N_Private_Type_Declaration
            | N_Protected_Type_Declaration
         =>
            null;

         --  The following nodes are rewritten by semantic analysis

         when N_Expression_Function =>
            raise Program_Error;
      end case;
   end Check_Declaration;

   ------------------
   -- Check_Entity --
   ------------------

   procedure Check_Entity (E : Entity_Id) is

      --  Local subprograms

      procedure Initialize;
      --  Initialize global variables before starting the analysis of a body

      ----------------
      -- Initialize --
      ----------------

      procedure Initialize is
      begin
         Reset (Current_Loops_Envs);
         Reset (Current_Loops_Accumulators);
         Reset (Current_Perm_Env);
      end Initialize;

   --  Start of processing for Check_Entity

   begin
      Initialize;
      case Ekind (E) is
         when Type_Kind =>
            if Ekind (E) in E_Task_Type | E_Protected_Type
              and then Entity_Body_In_SPARK (E)
            then
               Check_Callable_Body (E);
            end if;

         when Object_Kind =>

            null;

         when E_Entry
            | E_Function
            | E_Procedure
            =>
            if Entity_Body_In_SPARK (E) then
               Check_Callable_Body (E);
            end if;

         when E_Package =>
            declare
               Scope : constant Entity_Id :=
                 (if Is_Compilation_Unit (E) then Empty
                  else Enclosing_Unit (E));

            begin
               --  Only check a package entity if its enclosing unit is not
               --  already checked. Otherwise, E will be checked in the
               --  context of its scope.

               if Present (Scope) and then Entity_Spec_In_SPARK (Scope) then
                  pragma Assert
                    (for some E of Entities_To_Translate => E = Scope);
               else
                  pragma Assert
                    (for all E of Entities_To_Translate => E /= Scope);
                  Check_Package_Entity (E);
               end if;
            end;
         when E_Loop =>
            null;

         when others =>
            raise Program_Error;
      end case;
   end Check_Entity;

   -----------------------
   -- Check_Expr_Or_Ent --
   -----------------------

   procedure Check_Expr_Or_Ent
     (Expr : Expr_Or_Ent;
      Mode : Extended_Checking_Mode)
   is
   begin
      if Expr.Is_Ent then
         if Mode /= Read_Subexpr then
            Process_Path (Expr, Mode);
         end if;
      else
         Check_Expression (Expr.Expr, Mode);
      end if;
   end Check_Expr_Or_Ent;

   ----------------------
   -- Check_Expression --
   ----------------------

   procedure Check_Expression
     (Expr : Node_Id;
      Mode : Extended_Checking_Mode)
   is
      --  Local subprograms

      function Is_Type_Name (Expr : Node_Id) return Boolean;
      --  Detect when a path expression is in fact a type name

      procedure Move_Expression (Expr : Node_Id);
      --  Some subexpressions are only analyzed in Move mode. This is a
      --  specialized version of Check_Expression for that case.

      procedure Move_Expression_List (L : List_Id);
      --  Call Move_Expression on every expression in the list L

      procedure Read_Expression (Expr : Node_Id);
      --  Most subexpressions are only analyzed in Read mode. This is a
      --  specialized version of Check_Expression for that case.

      procedure Read_Expression_List (L : List_Id);
      --  Call Read_Expression on every expression in the list L

      procedure Read_Indexes (Expr : Node_Id);
      --  When processing a path, the index expressions and function call
      --  arguments occurring on the path should be analyzed in Read mode.

      ------------------
      -- Is_Type_Name --
      ------------------

      function Is_Type_Name (Expr : Node_Id) return Boolean is
      begin
         return Nkind_In (Expr, N_Expanded_Name, N_Identifier)
           and then Is_Type (Entity (Expr));
      end Is_Type_Name;

      ---------------------
      -- Move_Expression --
      ---------------------

      --  Distinguish the case where the argument is a path expression that
      --  needs explicit moving.

      procedure Move_Expression (Expr : Node_Id) is
      begin
         if Is_Path_Expression (Expr) then
            Check_Expression (Expr, Move);
         else
            Read_Expression (Expr);
         end if;
      end Move_Expression;

      --------------------------
      -- Move_Expression_List --
      --------------------------

      procedure Move_Expression_List (L : List_Id) is
         N : Node_Id;
      begin
         N := First (L);
         while Present (N) loop
            Move_Expression (N);
            Next (N);
         end loop;
      end Move_Expression_List;

      ---------------------
      -- Read_Expression --
      ---------------------

      procedure Read_Expression (Expr : Node_Id) is
      begin
         Check_Expression (Expr, Read);
      end Read_Expression;

      --------------------------
      -- Read_Expression_List --
      --------------------------

      procedure Read_Expression_List (L : List_Id) is
         N : Node_Id;
      begin
         N := First (L);
         while Present (N) loop
            Read_Expression (N);
            Next (N);
         end loop;
      end Read_Expression_List;

      ------------------
      -- Read_Indexes --
      ------------------

      procedure Read_Indexes (Expr : Node_Id) is

         --  Local subprograms

         procedure Read_Param (Formal : Entity_Id; Actual : Node_Id);
         --  Call Read_Expression on the actual

         ----------------
         -- Read_Param --
         ----------------

         procedure Read_Param (Formal : Entity_Id; Actual : Node_Id) is
            pragma Unreferenced (Formal);
         begin
            Read_Expression (Actual);
         end Read_Param;

         procedure Read_Params is new Iterate_Call_Parameters (Read_Param);

      --  Start of processing for Read_Indexes

      begin
         pragma Assert (Is_Subpath_Expression (Expr));

         case N_Subexpr'(Nkind (Expr)) is
            when N_Identifier
               | N_Expanded_Name
               | N_Null
            =>
               null;

            when N_Explicit_Dereference
               | N_Selected_Component
            =>
               Read_Indexes (Prefix (Expr));

            when N_Indexed_Component =>
               Read_Indexes (Prefix (Expr));
               Read_Expression_List (Expressions (Expr));

            when N_Slice =>
               Read_Indexes (Prefix (Expr));
               Read_Expression (Discrete_Range (Expr));

            --  The argument of an allocator is moved as part of the implicit
            --  assignment.

            when N_Allocator =>
               Move_Expression (Expression (Expr));

            when N_Function_Call =>
               Read_Params (Expr);
               if Ekind (Get_Called_Entity (Expr)) = E_Subprogram_Type then
                  raise Program_Error;
               else
                  Check_Globals (Get_Called_Entity (Expr), Expr);
               end if;

            when N_Op_Concat =>
               Read_Expression (Left_Opnd (Expr));
               Read_Expression (Right_Opnd (Expr));

            when N_Qualified_Expression
               | N_Type_Conversion
               | N_Unchecked_Type_Conversion
            =>
               Read_Indexes (Expression (Expr));

            when N_Aggregate =>
               declare
                  Assocs : constant List_Id := Component_Associations (Expr);
                  CL     : List_Id;
                  Assoc  : Node_Id := Nlists.First (Assocs);
                  Choice : Node_Id;

               begin
                  --  The subexpressions of an aggregate are moved as part
                  --  of the implicit assignments. Handle the positional
                  --  components first.

                  Move_Expression_List (Expressions (Expr));

                  --  Handle the named components next

                  while Present (Assoc) loop
                     CL := Choices (Assoc);

                     --  For an array aggregate, we should also check that the
                     --  expressions used in choices are readable.

                     if Is_Array_Type (Etype (Expr)) then
                        Choice := Nlists.First (CL);
                        while Present (Choice) loop
                           if Nkind (Choice) /= N_Others_Choice then
                              Read_Expression (Choice);
                           end if;
                           Next (Choice);
                        end loop;
                     end if;

                     --  The subexpressions of an aggregate are moved as part
                     --  of the implicit assignments.

                     if not Box_Present (Assoc) then
                        Move_Expression (Expression (Assoc));
                     end if;

                     Next (Assoc);
                  end loop;
               end;

            when N_Extension_Aggregate =>
               declare
                  Exprs  : constant List_Id := Expressions (Expr);
                  Assocs : constant List_Id := Component_Associations (Expr);
                  CL     : List_Id;
                  Assoc  : Node_Id := Nlists.First (Assocs);

               begin
                  Move_Expression (Ancestor_Part (Expr));

                  --  No positional components allowed at this stage

                  if Present (Exprs) then
                     raise Program_Error;
                  end if;

                  while Present (Assoc) loop
                     CL := Choices (Assoc);

                     --  Only singleton components allowed at this stage

                     if not Is_Singleton_Choice (CL) then
                        raise Program_Error;
                     end if;

                     --  The subexpressions of an aggregate are moved as part
                     --  of the implicit assignments.

                     if not Box_Present (Assoc) then
                        Move_Expression (Expression (Assoc));
                     end if;

                     Next (Assoc);
                  end loop;
               end;

            when N_If_Expression =>
               declare
                  Cond      : constant Node_Id := First (Expressions (Expr));
                  Then_Part : constant Node_Id := Next (Cond);
                  Else_Part : constant Node_Id := Next (Then_Part);
               begin
                  Read_Expression (Cond);
                  Read_Indexes (Then_Part);
                  Read_Indexes (Else_Part);
               end;

            when N_Case_Expression =>
               declare
                  Cases    : constant List_Id := Alternatives (Expr);
                  Cur_Case : Node_Id := First (Cases);

               begin
                  Read_Expression (Expression (Expr));

                  while Present (Cur_Case) loop
                     Read_Indexes (Expression (Cur_Case));
                     Next (Cur_Case);
                  end loop;
               end;

            when N_Attribute_Reference =>
               pragma Assert
                 (Get_Attribute_Id (Attribute_Name (Expr)) =
                    Attribute_Loop_Entry
                  or else
                  Get_Attribute_Id (Attribute_Name (Expr)) = Attribute_Update
                  or else
                  Get_Attribute_Id (Attribute_Name (Expr)) = Attribute_Image
                  or else
                  Get_Attribute_Id (Attribute_Name (Expr)) = Attribute_Img);

               Read_Expression (Prefix (Expr));

               if Get_Attribute_Id (Attribute_Name (Expr)) = Attribute_Update
                 or else (Get_Attribute_Id (Attribute_Name (Expr)) in
                            Attribute_Image | Attribute_Img
                          and then Is_Type_Name (Prefix (Expr)))
               then
                  Read_Expression_List (Expressions (Expr));
               end if;

            when others =>
               raise Program_Error;
         end case;
      end Read_Indexes;

   --  Start of processing for Check_Expression

   begin
      if Is_Type_Name (Expr) then
         return;

      elsif Is_Path_Expression (Expr) then
         if Mode /= Assign then
            Read_Indexes (Expr);
         end if;

         if Mode /= Read_Subexpr then
            Process_Path (+Expr, Mode);
         end if;

         return;
      end if;

      --  Expressions that are not path expressions should only be analyzed in
      --  Read mode.

      pragma Assert (Mode = Read);

      --  Special handling for nodes that may contain evaluated expressions in
      --  the form of constraints.

      case Nkind (Expr) is
         when N_Index_Or_Discriminant_Constraint =>
            declare
               Assn : Node_Id := First (Constraints (Expr));
            begin
               while Present (Assn) loop
                  case Nkind (Assn) is
                     when N_Discriminant_Association =>
                        Read_Expression (Expression (Assn));

                     when others =>
                        Read_Expression (Assn);
                  end case;

                  Next (Assn);
               end loop;
            end;
            return;

         when N_Range_Constraint =>
            Read_Expression (Range_Expression (Expr));
            return;

         when N_Subtype_Indication =>
            if Present (Constraint (Expr)) then
               Read_Expression (Constraint (Expr));
            end if;
            return;

         when N_Digits_Constraint =>
            Read_Expression (Digits_Expression (Expr));
            if Present (Range_Constraint (Expr)) then
               Read_Expression (Range_Constraint (Expr));
            end if;
            return;

         when N_Delta_Constraint =>
            Read_Expression (Delta_Expression (Expr));
            if Present (Range_Constraint (Expr)) then
               Read_Expression (Range_Constraint (Expr));
            end if;
            return;

         when others =>
            null;
      end case;

      --  At this point Expr can only be a subexpression

      case N_Subexpr'(Nkind (Expr)) is

         when N_Binary_Op
            | N_Short_Circuit
         =>
            Read_Expression (Left_Opnd (Expr));
            Read_Expression (Right_Opnd (Expr));

         when N_Membership_Test =>
            Read_Expression (Left_Opnd (Expr));
            if Present (Right_Opnd (Expr)) then
               Read_Expression (Right_Opnd (Expr));
            else
               declare
                  Cases    : constant List_Id := Alternatives (Expr);
                  Cur_Case : Node_Id := First (Cases);

               begin
                  while Present (Cur_Case) loop
                     Read_Expression (Cur_Case);
                     Next (Cur_Case);
                  end loop;
               end;
            end if;

         when N_Unary_Op =>
            Read_Expression (Right_Opnd (Expr));

         when N_Attribute_Reference =>
            declare
               Aname   : constant Name_Id := Attribute_Name (Expr);
               Attr_Id : constant Attribute_Id := Get_Attribute_Id (Aname);
               Pref    : constant Node_Id := Prefix (Expr);
               Args    : constant List_Id := Expressions (Expr);

            begin
               case Attr_Id is

                  --  The following attributes take either no arguments, or
                  --  arguments that do not refer to evaluated expressions
                  --  (like Length or Loop_Entry), hence only the prefix
                  --  needs to be read.

                  when Attribute_Address
                     | Attribute_Alignment
                     | Attribute_Callable
                     | Attribute_Component_Size
                     | Attribute_Constrained
                     | Attribute_First
                     | Attribute_First_Bit
                     | Attribute_Last
                     | Attribute_Last_Bit
                     | Attribute_Length
                     | Attribute_Loop_Entry
                     | Attribute_Object_Size
                     | Attribute_Position
                     | Attribute_Size
                     | Attribute_Terminated
                     | Attribute_Valid
                     | Attribute_Value_Size
                  =>
                     Read_Expression (Pref);

                  --  The following attributes take a type name as prefix,
                  --  hence only the arguments need to be read.

                  when Attribute_Ceiling
                     | Attribute_Floor
                     | Attribute_Max
                     | Attribute_Min
                     | Attribute_Mod
                     | Attribute_Pos
                     | Attribute_Pred
                     | Attribute_Remainder
                     | Attribute_Rounding
                     | Attribute_Succ
                     | Attribute_Truncation
                     | Attribute_Val
                     | Attribute_Value
                  =>
                     Read_Expression_List (Args);

                  --  Attributes Image and Img either take a type name as
                  --  prefix with an expression in argument, or the expression
                  --  directly as prefix. Adapt to each case.

                  when Attribute_Image
                     | Attribute_Img
                  =>
                     if No (Args) then
                        Read_Expression (Pref);
                     else
                        Read_Expression_List (Args);
                     end if;

                  --  Attribute Update takes expressions as both prefix and
                  --  arguments, so both need to be read.

                  when Attribute_Update =>
                     Read_Expression (Pref);
                     Read_Expression_List (Args);

                  --  Attribute Modulus does not reference the evaluated
                  --  expression, so it can be ignored for this analysis.

                  when Attribute_Modulus =>
                     null;

                  --  The following attributes apply to types; there are no
                  --  expressions to read.

                  when Attribute_Class
                     | Attribute_Storage_Size
                  =>
                     null;

                  --  Postconditions should not be analyzed

                  when Attribute_Old
                     | Attribute_Result
                  =>
                     raise Program_Error;

                  when others =>
                     null;
               end case;
            end;

         when N_Range =>
            Read_Expression (Low_Bound (Expr));
            Read_Expression (High_Bound (Expr));

         when N_If_Expression =>
            Read_Expression_List (Expressions (Expr));

         when N_Case_Expression =>
            declare
               Cases    : constant List_Id := Alternatives (Expr);
               Cur_Case : Node_Id := First (Cases);

            begin
               while Present (Cur_Case) loop
                  Read_Expression (Expression (Cur_Case));
                  Next (Cur_Case);
               end loop;

               Read_Expression (Expression (Expr));
            end;

         when N_Qualified_Expression
            | N_Type_Conversion
            | N_Unchecked_Type_Conversion
         =>
            Read_Expression (Expression (Expr));

         when N_Quantified_Expression =>
            declare
               For_In_Spec : constant Node_Id :=
                 Loop_Parameter_Specification (Expr);
               For_Of_Spec : constant Node_Id :=
                 Iterator_Specification (Expr);
               For_Of_Spec_Typ : Node_Id;

            begin
               if Present (For_In_Spec) then
                  Read_Expression (Discrete_Subtype_Definition (For_In_Spec));
               else
                  Read_Expression (Name (For_Of_Spec));
                  For_Of_Spec_Typ := Subtype_Indication (For_Of_Spec);
                  if Present (For_Of_Spec_Typ) then
                     Read_Expression (For_Of_Spec_Typ);
                  end if;
               end if;

               Read_Expression (Condition (Expr));
            end;

         when N_Character_Literal
            | N_Numeric_Or_String_Literal
            | N_Operator_Symbol
            | N_Raise_Expression
            | N_Raise_xxx_Error
         =>
            null;

         when N_Delta_Aggregate
            | N_Target_Name
         =>
            null;

         --  Procedure calls are handled in Check_Node

         when N_Procedure_Call_Statement =>
            raise Program_Error;

         --  Path expressions are handled before this point

         when N_Aggregate
            | N_Allocator
            | N_Expanded_Name
            | N_Explicit_Dereference
            | N_Extension_Aggregate
            | N_Function_Call
            | N_Identifier
            | N_Indexed_Component
            | N_Null
            | N_Selected_Component
            | N_Slice
         =>
            raise Program_Error;

         --  The following nodes are never generated in GNATprove mode

         when N_Expression_With_Actions
            | N_Reference
            | N_Unchecked_Expression
         =>
            raise Program_Error;
      end case;
   end Check_Expression;

   ----------------
   -- Check_List --
   ----------------

   procedure Check_List (L : List_Id) is
      N : Node_Id;
   begin
      N := First (L);
      while Present (N) loop
         Check_Node (N);
         Next (N);
      end loop;
   end Check_List;

   --------------------------
   -- Check_Loop_Statement --
   --------------------------

   procedure Check_Loop_Statement (Stmt : Node_Id) is

      --  Local Subprograms

      procedure Check_Is_Less_Restrictive_Env
        (Exiting_Env : Perm_Env;
         Entry_Env   : Perm_Env);
      --  This procedure checks that the Exiting_Env environment is less
      --  restrictive than the Entry_Env environment.

      procedure Check_Is_Less_Restrictive_Tree
        (New_Tree  : Perm_Tree_Access;
         Orig_Tree : Perm_Tree_Access;
         E         : Entity_Id);
      --  Auxiliary procedure to check that the tree New_Tree is less
      --  restrictive than the tree Orig_Tree for the entity E.

      procedure Perm_Error_Loop_Exit
        (E          : Entity_Id;
         Loop_Id    : Node_Id;
         Perm       : Perm_Kind;
         Found_Perm : Perm_Kind;
         Expl       : Node_Id);
      --  A procedure that is called when the permissions found contradict
      --  the rules established by the RM at the exit of loops. This function
      --  is called with the entity, the node of the enclosing loop, the
      --  permission that was expected, and the permission found, and issues
      --  an appropriate error message.

      -----------------------------------
      -- Check_Is_Less_Restrictive_Env --
      -----------------------------------

      procedure Check_Is_Less_Restrictive_Env
        (Exiting_Env : Perm_Env;
         Entry_Env   : Perm_Env)
      is
         Comp_Entry : Perm_Tree_Maps.Key_Option;
         Iter_Entry, Iter_Exit : Perm_Tree_Access;

      begin
         Comp_Entry := Get_First_Key (Entry_Env);
         while Comp_Entry.Present loop
            Iter_Entry := Get (Entry_Env, Comp_Entry.K);
            pragma Assert (Iter_Entry /= null);
            Iter_Exit := Get (Exiting_Env, Comp_Entry.K);
            pragma Assert (Iter_Exit /= null);
            Check_Is_Less_Restrictive_Tree
              (New_Tree  => Iter_Exit,
               Orig_Tree => Iter_Entry,
               E         => Comp_Entry.K);
            Comp_Entry := Get_Next_Key (Entry_Env);
         end loop;
      end Check_Is_Less_Restrictive_Env;

      ------------------------------------
      -- Check_Is_Less_Restrictive_Tree --
      ------------------------------------

      procedure Check_Is_Less_Restrictive_Tree
        (New_Tree  : Perm_Tree_Access;
         Orig_Tree : Perm_Tree_Access;
         E         : Entity_Id)
      is
         --  Local subprograms

         procedure Check_Is_Less_Restrictive_Tree_Than
           (Tree : Perm_Tree_Access;
            Perm : Perm_Kind;
            E    : Entity_Id);
         --  Auxiliary procedure to check that the tree N is less restrictive
         --  than the given permission P.

         procedure Check_Is_More_Restrictive_Tree_Than
           (Tree : Perm_Tree_Access;
            Perm : Perm_Kind;
            E    : Entity_Id);
         --  Auxiliary procedure to check that the tree N is more restrictive
         --  than the given permission P.

         -----------------------------------------
         -- Check_Is_Less_Restrictive_Tree_Than --
         -----------------------------------------

         procedure Check_Is_Less_Restrictive_Tree_Than
           (Tree : Perm_Tree_Access;
            Perm : Perm_Kind;
            E    : Entity_Id)
         is
         begin
            if not (Permission (Tree) >= Perm) then
               Perm_Error_Loop_Exit
                 (E, Stmt, Permission (Tree), Perm, Explanation (Tree));
            end if;

            case Kind (Tree) is
               when Entire_Object =>
                  if not (Children_Permission (Tree) >= Perm) then
                     Perm_Error_Loop_Exit
                       (E, Stmt, Children_Permission (Tree), Perm,
                        Explanation (Tree));

                  end if;

               when Reference =>
                  Check_Is_Less_Restrictive_Tree_Than
                    (Get_All (Tree), Perm, E);

               when Array_Component =>
                  Check_Is_Less_Restrictive_Tree_Than
                    (Get_Elem (Tree), Perm, E);

               when Record_Component =>
                  declare
                     Comp : Perm_Tree_Access;
                  begin
                     Comp := Perm_Tree_Maps.Get_First (Component (Tree));
                     while Comp /= null loop
                        Check_Is_Less_Restrictive_Tree_Than (Comp, Perm, E);
                        Comp :=
                          Perm_Tree_Maps.Get_Next (Component (Tree));
                     end loop;
                  end;
            end case;
         end Check_Is_Less_Restrictive_Tree_Than;

         -----------------------------------------
         -- Check_Is_More_Restrictive_Tree_Than --
         -----------------------------------------

         procedure Check_Is_More_Restrictive_Tree_Than
           (Tree : Perm_Tree_Access;
            Perm : Perm_Kind;
            E    : Entity_Id)
         is
         begin
            if not (Perm >= Permission (Tree)) then
               Perm_Error_Loop_Exit
                 (E, Stmt, Permission (Tree), Perm, Explanation (Tree));
            end if;

            case Kind (Tree) is
               when Entire_Object =>
                  if not (Perm >= Children_Permission (Tree)) then
                     Perm_Error_Loop_Exit
                       (E, Stmt, Children_Permission (Tree), Perm,
                        Explanation (Tree));
                  end if;

               when Reference =>
                  Check_Is_More_Restrictive_Tree_Than
                    (Get_All (Tree), Perm, E);

               when Array_Component =>
                  Check_Is_More_Restrictive_Tree_Than
                    (Get_Elem (Tree), Perm, E);

               when Record_Component =>
                  declare
                     Comp : Perm_Tree_Access;
                  begin
                     Comp := Perm_Tree_Maps.Get_First (Component (Tree));
                     while Comp /= null loop
                        Check_Is_More_Restrictive_Tree_Than (Comp, Perm, E);
                        Comp :=
                          Perm_Tree_Maps.Get_Next (Component (Tree));
                     end loop;
                  end;
            end case;
         end Check_Is_More_Restrictive_Tree_Than;

      --  Start of processing for Check_Is_Less_Restrictive_Tree

      begin
         if not (Permission (New_Tree) <= Permission (Orig_Tree)) then
            Perm_Error_Loop_Exit
              (E          => E,
               Loop_Id    => Stmt,
               Perm       => Permission (New_Tree),
               Found_Perm => Permission (Orig_Tree),
               Expl       => Explanation (New_Tree));
         end if;

         case Kind (New_Tree) is

            --  Potentially folded tree. We check the other tree Orig_Tree to
            --  check whether it is folded or not. If folded we just compare
            --  their Permission and Children_Permission, if not, then we
            --  look at the Children_Permission of the folded tree against
            --  the unfolded tree Orig_Tree.

            when Entire_Object =>
               case Kind (Orig_Tree) is
               when Entire_Object =>
                  if not (Children_Permission (New_Tree) <=
                          Children_Permission (Orig_Tree))
                  then
                     Perm_Error_Loop_Exit
                       (E, Stmt,
                        Children_Permission (New_Tree),
                        Children_Permission (Orig_Tree),
                        Explanation (New_Tree));
                  end if;

               when Reference =>
                  Check_Is_More_Restrictive_Tree_Than
                    (Get_All (Orig_Tree), Children_Permission (New_Tree), E);

               when Array_Component =>
                  Check_Is_More_Restrictive_Tree_Than
                    (Get_Elem (Orig_Tree), Children_Permission (New_Tree), E);

               when Record_Component =>
                  declare
                     Comp : Perm_Tree_Access;
                  begin
                     Comp := Perm_Tree_Maps.Get_First
                       (Component (Orig_Tree));
                     while Comp /= null loop
                        Check_Is_More_Restrictive_Tree_Than
                          (Comp, Children_Permission (New_Tree), E);
                        Comp := Perm_Tree_Maps.Get_Next
                          (Component (Orig_Tree));
                     end loop;
                  end;
               end case;

            when Reference =>
               case Kind (Orig_Tree) is
               when Entire_Object =>
                  Check_Is_Less_Restrictive_Tree_Than
                    (Get_All (New_Tree), Children_Permission (Orig_Tree), E);

               when Reference =>
                  Check_Is_Less_Restrictive_Tree
                    (Get_All (New_Tree), Get_All (Orig_Tree), E);

               when others =>
                  raise Program_Error;
               end case;

            when Array_Component =>
               case Kind (Orig_Tree) is
               when Entire_Object =>
                  Check_Is_Less_Restrictive_Tree_Than
                    (Get_Elem (New_Tree), Children_Permission (Orig_Tree), E);

               when Array_Component =>
                  Check_Is_Less_Restrictive_Tree
                    (Get_Elem (New_Tree), Get_Elem (Orig_Tree), E);

               when others =>
                  raise Program_Error;
               end case;

            when Record_Component =>
               declare
                  CompN : Perm_Tree_Access;
               begin
                  CompN :=
                    Perm_Tree_Maps.Get_First (Component (New_Tree));
                  case Kind (Orig_Tree) is
                  when Entire_Object =>
                     while CompN /= null loop
                        Check_Is_Less_Restrictive_Tree_Than
                          (CompN, Children_Permission (Orig_Tree), E);

                        CompN :=
                          Perm_Tree_Maps.Get_Next (Component (New_Tree));
                     end loop;

                  when Record_Component =>
                     declare

                        KeyO : Perm_Tree_Maps.Key_Option;
                        CompO : Perm_Tree_Access;
                     begin
                        KeyO := Perm_Tree_Maps.Get_First_Key
                          (Component (Orig_Tree));
                        while KeyO.Present loop
                           CompN := Perm_Tree_Maps.Get
                             (Component (New_Tree), KeyO.K);
                           CompO := Perm_Tree_Maps.Get
                             (Component (Orig_Tree), KeyO.K);
                           pragma Assert (CompO /= null);

                           Check_Is_Less_Restrictive_Tree (CompN, CompO, E);

                           KeyO := Perm_Tree_Maps.Get_Next_Key
                             (Component (Orig_Tree));
                        end loop;
                     end;

                  when others =>
                     raise Program_Error;
                  end case;
               end;
         end case;
      end Check_Is_Less_Restrictive_Tree;

      --------------------------
      -- Perm_Error_Loop_Exit --
      --------------------------

      procedure Perm_Error_Loop_Exit
        (E          : Entity_Id;
         Loop_Id    : Node_Id;
         Perm       : Perm_Kind;
         Found_Perm : Perm_Kind;
         Expl       : Node_Id)
      is
      begin
         Error_Msg_Node_2 := Loop_Id;
         Error_Msg_N
           ("insufficient permission for & when exiting loop &", E);
         Perm_Mismatch (Exp_Perm => Perm,
                        Act_Perm => Found_Perm,
                        N        => Loop_Id,
                        Expl     => Expl);
         Permission_Error := True;
      end Perm_Error_Loop_Exit;

      --  Local variables

      Loop_Name : constant Entity_Id := Entity (Identifier (Stmt));
      Loop_Env  : constant Perm_Env_Access := new Perm_Env;
      Scheme    : constant Node_Id := Iteration_Scheme (Stmt);

   --  Start of processing for Check_Loop_Statement

   begin
      --  Save environment prior to the loop

      Copy_Env (From => Current_Perm_Env, To => Loop_Env.all);

      --  Add saved environment to loop environment

      Set (Current_Loops_Envs, Loop_Name, Loop_Env);

      --  If the loop is not a plain-loop, then it may either never be entered,
      --  or it may be exited after a number of iterations. Hence add the
      --  current permission environment as the initial loop exit environment.
      --  Otherwise, the loop exit environment remains empty until it is
      --  populated by analyzing exit statements.

      if Present (Iteration_Scheme (Stmt)) then
         declare
            Exit_Env : constant Perm_Env_Access := new Perm_Env;

         begin
            Copy_Env (From => Current_Perm_Env, To => Exit_Env.all);
            Set (Current_Loops_Accumulators, Loop_Name, Exit_Env);
         end;
      end if;

      --  Analyze loop

      if Present (Scheme) then

         --  Case of a WHILE loop

         if Present (Condition (Scheme)) then
            Check_Expression (Condition (Scheme), Read);

         --  Case of a FOR loop

         else
            declare
               Param_Spec : constant Node_Id :=
                 Loop_Parameter_Specification (Scheme);
               Iter_Spec : constant Node_Id := Iterator_Specification (Scheme);
            begin
               if Present (Param_Spec) then
                  Check_Expression
                    (Discrete_Subtype_Definition (Param_Spec), Read);
               else
                  Check_Expression (Name (Iter_Spec), Read);
                  if Present (Subtype_Indication (Iter_Spec)) then
                     Check_Expression (Subtype_Indication (Iter_Spec), Read);
                  end if;
               end if;
            end;
         end if;
      end if;

      Check_List (Statements (Stmt));

      --  Check that environment gets less restrictive at end of loop

      Check_Is_Less_Restrictive_Env
        (Exiting_Env => Current_Perm_Env,
         Entry_Env   => Loop_Env.all);

      --  Set environment to the one for exiting the loop

      declare
         Exit_Env : constant Perm_Env_Access :=
           Get (Current_Loops_Accumulators, Loop_Name);
      begin
         Free_Env (Current_Perm_Env);

         --  In the normal case, Exit_Env is not null and we use it. In the
         --  degraded case of a plain-loop without exit statements, Exit_Env is
         --  null, and we use the initial permission environment at the start
         --  of the loop to continue analysis. Any environment would be fine
         --  here, since the code after the loop is dead code, but this way we
         --  avoid spurious errors by having at least variables in scope inside
         --  the environment.

         if Exit_Env /= null then
            Copy_Env (From => Exit_Env.all, To => Current_Perm_Env);
            Free_Env (Loop_Env.all);
            Free_Env (Exit_Env.all);
         else
            Copy_Env (From => Loop_Env.all, To => Current_Perm_Env);
            Free_Env (Loop_Env.all);
         end if;
      end;
   end Check_Loop_Statement;

   ----------------
   -- Check_Node --
   ----------------

   procedure Check_Node (N : Node_Id) is

   --  Start of processing for Check_Node

   begin
      case Nkind (N) is
         when N_Declaration =>
            Check_Declaration (N);

         when N_Body_Stub =>
            null;

         when N_Statement_Other_Than_Procedure_Call =>
            Check_Statement (N);

         when N_Procedure_Call_Statement =>
            Check_Call_Statement (N);

         when N_Package_Body =>
            declare
               Id : constant Entity_Id := Unique_Defining_Entity (N);
            begin
               if Ekind (Id) = E_Package
                 and then Entity_In_SPARK (Id)
                 and then Entity_Body_In_SPARK (Id)
               then
                  Check_Package_Body (Id);
               end if;
            end;

         when N_Subprogram_Body =>
            null;

         when N_Entry_Body
            | N_Task_Body
         =>
            null;

         when N_Protected_Body =>
            null;

         when N_Package_Declaration =>
            declare
               Id : constant Entity_Id := Defining_Entity (N);
            begin
               if Entity_In_SPARK (Id) then
                  Check_Package_Spec (Id);
               end if;
            end;

         when N_Handled_Sequence_Of_Statements =>
            Check_List (Statements (N));

         when N_Pragma =>
            Check_Pragma (N);

         when N_Subprogram_Declaration =>
            null;

         --  Attribute references in statement position are not supported in
         --  SPARK and will be rejected by GNATprove.

         when N_Attribute_Reference =>
            null;

         --  Ignored constructs for pointer checking

         when N_Abstract_Subprogram_Declaration
            | N_At_Clause
            | N_Attribute_Definition_Clause
            | N_Call_Marker
            | N_Delta_Constraint
            | N_Digits_Constraint
            | N_Empty
            | N_Enumeration_Representation_Clause
            | N_Exception_Declaration
            | N_Exception_Renaming_Declaration
            | N_Formal_Package_Declaration
            | N_Formal_Subprogram_Declaration
            | N_Freeze_Entity
            | N_Freeze_Generic_Entity
            | N_Function_Instantiation
            | N_Generic_Function_Renaming_Declaration
            | N_Generic_Package_Declaration
            | N_Generic_Package_Renaming_Declaration
            | N_Generic_Procedure_Renaming_Declaration
            | N_Generic_Subprogram_Declaration
            | N_Implicit_Label_Declaration
            | N_Itype_Reference
            | N_Label
            | N_Number_Declaration
            | N_Object_Renaming_Declaration
            | N_Others_Choice
            | N_Package_Instantiation
            | N_Package_Renaming_Declaration
            | N_Procedure_Instantiation
            | N_Raise_xxx_Error
            | N_Record_Representation_Clause
            | N_Subprogram_Renaming_Declaration
            | N_Task_Type_Declaration
            | N_Use_Package_Clause
            | N_With_Clause
            | N_Use_Type_Clause
            | N_Validate_Unchecked_Conversion
            | N_Variable_Reference_Marker
            | N_Discriminant_Association

            --  ??? check whether we should do something special for
            --  N_Discriminant_Association, or maybe raise Program_Error.
         =>
            null;

         --  Checking should not be called directly on these nodes

         when others =>
            raise Program_Error;
      end case;
   end Check_Node;

   ------------------------
   -- Check_Not_Borrowed --
   ------------------------

   procedure Check_Not_Borrowed (Expr : Expr_Or_Ent; Root : Entity_Id) is
   begin
      --  An expression without root object cannot be borrowed

      if No (Root) then
         return;
      end if;

      --  Otherwise, try to match the expression with one of the borrowed
      --  expressions.

      declare
         Key      : Variable_Maps.Key_Option :=
           Get_First_Key (Current_Borrowers);
         Var      : Entity_Id;
         Borrowed : Node_Id;
         B_Pledge : Entity_Id := Empty;

      begin
         if not Expr.Is_Ent then

            --  Search for a call to a pledge function in the parents of
            --  Expr.

            declare
               Call : Node_Id := Expr.Expr;
            begin
               while Present (Call)
                 and then
                   (Nkind (Call) /= N_Function_Call
                    or else
                      not Has_Pledge_Annotation (Get_Called_Entity (Call)))
               loop
                  Call := Parent (Call);
               end loop;

               if Present (Call)
                 and then Nkind (First_Actual (Call)) in N_Has_Entity
               then
                  B_Pledge := Entity (First_Actual (Call));
               end if;
            end;
         end if;

         while Key.Present loop
            Var := Key.K;
            Borrowed := Get (Current_Borrowers, Var);

            if Is_Prefix_Or_Almost (Pref => Borrowed, Expr => Expr)
              and then Var /= B_Pledge
            then
               Error_Msg_Sloc := Sloc (Borrowed);
               if Expr.Is_Ent then
                  Error_Msg_NE ("& was borrowed #", Expr.Loc, Expr.Ent);
               else
                  Error_Msg_N ("object was borrowed #", Expr.Expr);
               end if;
               Permission_Error := True;
            end if;

            Key := Get_Next_Key (Current_Borrowers);
         end loop;
      end;
   end Check_Not_Borrowed;

   ------------------------
   -- Check_Not_Observed --
   ------------------------

   procedure Check_Not_Observed (Expr : Expr_Or_Ent; Root : Entity_Id) is
   begin
      --  An expression without root object cannot be observed

      if No (Root) then
         return;
      end if;

      --  Otherwise, try to match the expression with one of the observed
      --  expressions.

      declare
         Key      : Variable_Maps.Key_Option :=
           Get_First_Key (Current_Observers);
         Var      : Entity_Id;
         Observed : Node_Id;

      begin
         while Key.Present loop
            Var := Key.K;
            Observed := Get (Current_Observers, Var);

            if Is_Prefix_Or_Almost (Pref => Observed, Expr => Expr) then
               Error_Msg_Sloc := Sloc (Observed);
               if Expr.Is_Ent then
                  Error_Msg_NE ("& was observed #", Expr.Loc, Expr.Ent);
               else
                  Error_Msg_N ("object was observed #", Expr.Expr);
               end if;
               Permission_Error := True;
            end if;

            Key := Get_Next_Key (Current_Observers);
         end loop;
      end;
   end Check_Not_Observed;

   ------------------------
   -- Check_Package_Body --
   ------------------------

   procedure Check_Package_Body (Id : Entity_Id) is
      Save_In_Elab : constant Boolean := Inside_Elaboration;
      Body_N       : constant Node_Id := Package_Body (Id);
      Saved_Env    : Perm_Env;

   begin
      Inside_Elaboration := True;

      --  Save environment

      Copy_Env (Current_Perm_Env, Saved_Env);

      --  Check declarations and statements in the special mode for
      --  elaboration.

      if Entity_Body_In_SPARK (Id) then
         Check_List (Declarations (Body_N));

         Check_Node (Handled_Statement_Sequence (Body_N));
      end if;

      --  Restore the saved environment and free the current one

      Move_Env (Saved_Env, Current_Perm_Env);

      Inside_Elaboration := Save_In_Elab;
   end Check_Package_Body;

   --------------------------
   -- Check_Package_Entity --
   --------------------------

   procedure Check_Package_Entity (Id : Entity_Id) is
      Saved_Env : Perm_Env;

   begin
      --  Save environment

      Move_Env (Current_Perm_Env, Saved_Env);

      --  Setup permissions for global variables referenced by Id

      Setup_Globals (Id);

      Check_Package_Spec (Id);

      if Entity_Body_In_SPARK (Id) then
         Check_Package_Body (Id);
      end if;

      --  Restore the saved environment and free the current one

      Move_Env (Saved_Env, Current_Perm_Env);
   end Check_Package_Entity;

   ------------------------
   -- Check_Package_Spec --
   ------------------------

   procedure Check_Package_Spec (Id : Entity_Id) is
      Save_In_Elab : constant Boolean := Inside_Elaboration;
      Spec         : constant Node_Id := Package_Specification (Id);
      Vis_Decls    : constant List_Id := Visible_Declarations (Spec);
      Priv_Decls   : constant List_Id := Private_Declarations (Spec);

   begin
      Inside_Elaboration := True;

      --  Check declarations in the special mode for elaboration

      if Present (Vis_Decls) then
         Check_List (Visible_Declarations (Spec));
      end if;

      if Present (Priv_Decls)
        and then Private_Spec_In_SPARK (Id)
      then
         Check_List (Private_Declarations (Spec));
      end if;

      Inside_Elaboration := Save_In_Elab;
   end Check_Package_Spec;

   -------------------------------
   -- Check_Parameter_Or_Global --
   -------------------------------

   procedure Check_Parameter_Or_Global
     (Expr       : Expr_Or_Ent;
      Typ        : Entity_Id;
      Kind       : Formal_Kind;
      Subp       : Entity_Id;
      Global_Var : Boolean)
   is
      Mode   : Checking_Mode;

   begin
      case Kind is
         when E_In_Parameter =>

            --  Inputs of functions have R permission only

            if Ekind (Subp) = E_Function then
               Mode := Read;

            --  Input global variables have R permission only

            elsif Global_Var then
               Mode := Read;

            --  Anonymous access to constant is an observe

            elsif Is_Anonymous_Access_Type (Typ)
              and then Is_Access_Constant (Typ)
            then
               Mode := Observe;

            --  Other access types are a borrow

            elsif Is_Access_Type (Typ) then
               Mode := Borrow;

            --  Deep types other than access types define an observe

            elsif Is_Deep (Typ) then
               Mode := Observe;

            --  Otherwise the variable is read

            else
               Mode := Read;
            end if;

         when E_Out_Parameter =>
            Mode := Assign;

         when E_In_Out_Parameter =>
            Mode := Move;
      end case;

      if Mode = Assign then
         Check_Expr_Or_Ent (Expr, Read_Subexpr);
      end if;

      Check_Expr_Or_Ent (Expr, Mode);
   end Check_Parameter_Or_Global;

   procedure Check_Globals_Inst is
     new Handle_Globals (Check_Parameter_Or_Global);

   procedure Check_Globals (Subp : Entity_Id; Loc : Node_Id) renames
     Check_Globals_Inst;

   ------------------
   -- Check_Pragma --
   ------------------

   procedure Check_Pragma (Prag : Node_Id) is
      Prag_Id : constant Pragma_Id := Get_Pragma_Id (Prag);
      Arg1    : constant Node_Id :=
        First (Pragma_Argument_Associations (Prag));
      Arg2    : Node_Id := Empty;

   begin
      if Present (Arg1) then
         Arg2 := Next (Arg1);
      end if;

      case Prag_Id is
         when Pragma_Check =>
            declare
               Expr : constant Node_Id := Expression (Arg2);
            begin
               Check_Expression (Expr, Read);
            end;

         --  There is no need to check contracts, as these can only access
         --  inputs and outputs of the subprogram. Inputs are checked
         --  independently for R permission. Outputs are checked
         --  independently to have RW permission on exit.

         --  Postconditions are checked for correct use of 'Old, but starting
         --  from the corresponding declaration, in order to avoid dealing with
         --  with contracts on generic subprograms which are not handled in
         --  GNATprove.

         when Pragma_Loop_Variant
            | Pragma_Precondition
            | Pragma_Postcondition
            | Pragma_Contract_Cases
            | Pragma_Refined_Post
         =>
            null;

         --  The same holds for the initial condition after package
         --  elaboration, for the different reason that library-level
         --  variables can only be left in RW state after elaboration.

         when Pragma_Initial_Condition =>
            null;

         --  These pragmas should have been rewritten and/or removed in
         --  GNATprove mode.

         when Pragma_Assert
            | Pragma_Assert_And_Cut
            | Pragma_Assume
            | Pragma_Compile_Time_Error
            | Pragma_Compile_Time_Warning
            | Pragma_Debug
            | Pragma_Loop_Invariant
         =>
            raise Program_Error;

         when others =>
            null;
      end case;
   end Check_Pragma;

   ---------------------
   -- Check_Statement --
   ---------------------

   procedure Check_Statement (Stmt : Node_Id) is
   begin
      case N_Statement_Other_Than_Procedure_Call'(Nkind (Stmt)) is

         --  An entry call is handled like other calls

         when N_Entry_Call_Statement =>
            Check_Call_Statement (Stmt);

         --  An assignment may correspond to a move, a borrow, or an observe

         when N_Assignment_Statement =>
            declare
               Target : constant Node_Id := Name (Stmt);

            begin
               --  Start with checking that the subexpressions of the target
               --  path are readable, before possibly updating the permission
               --  of these subexpressions in Check_Assignment.

               Check_Expression (Target, Read_Subexpr);

               Check_Assignment (Target => Target,
                                 Expr   => Expression (Stmt));

               --  Local observers and borrowers can always be assigned, unless
               --  they are themselves observed/borrowed. We skip checking for
               --  them as observers have only read permission. Note that
               --  includes regular observers of access-to-constant type as
               --  well as observers of access-to-variable type inside
               --  traversal functions.

               if Is_Anonymous_Access_Type (Etype (Target)) then
                  declare
                     Root : constant Entity_Id := Get_Root_Object (Target);
                  begin
                     Check_Not_Observed (+Target, Root);
                     Check_Not_Borrowed (+Target, Root);
                  end;

               else
                  Check_Expression (Target, Assign);
               end if;
            end;

         when N_Block_Statement =>
            Check_List (Declarations (Stmt));
            Check_Node (Handled_Statement_Sequence (Stmt));

            --  Remove local borrowers and observers

            declare
               Decl : Node_Id := First (Declarations (Stmt));
               Var  : Entity_Id;
            begin
               while Present (Decl) loop
                  if Nkind (Decl) = N_Object_Declaration then
                     Var := Defining_Identifier (Decl);
                     Remove (Current_Borrowers, Var);
                     Remove (Current_Observers, Var);
                  end if;

                  Next (Decl);
               end loop;
            end;

         when N_Case_Statement =>
            declare
               Alt       : Node_Id;
               Saved_Env : Perm_Env;
               --  Copy of environment for analysis of the different cases
               New_Env   : Perm_Env;
               --  Accumulator for the different cases

            begin
               Check_Expression (Expression (Stmt), Read);

               --  Save environment

               Copy_Env (Current_Perm_Env, Saved_Env);

               --  First alternative

               Alt := First (Alternatives (Stmt));
               Check_List (Statements (Alt));
               Next (Alt);

               --  Cleanup

               Move_Env (Current_Perm_Env, New_Env);

               --  Other alternatives

               while Present (Alt) loop

                  --  Restore environment

                  Copy_Env (Saved_Env, Current_Perm_Env);

                  --  Next alternative

                  Check_List (Statements (Alt));
                  Next (Alt);

                  --  Merge Current_Perm_Env into New_Env

                  Merge_Env (Source => Current_Perm_Env, Target => New_Env);
               end loop;

               Move_Env (New_Env, Current_Perm_Env);
               Free_Env (Saved_Env);
            end;

         when N_Delay_Relative_Statement
            | N_Delay_Until_Statement
         =>
            Check_Expression (Expression (Stmt), Read);

         when N_Loop_Statement =>
            Check_Loop_Statement (Stmt);

         when N_Simple_Return_Statement =>
            declare
               Subp : constant Entity_Id :=
                 Return_Applies_To (Return_Statement_Entity (Stmt));
               Expr : constant Node_Id := Expression (Stmt);
            begin
               if Present (Expr) then
                  declare
                     Return_Typ : constant Entity_Id :=
                       Etype (Expr);

                  begin
                     --  SPARK RM 3.10(5): A return statement that applies
                     --  to a traversal function that has an anonymous
                     --  access-to-constant (respectively, access-to-variable)
                     --  result type, shall return either the literal null
                     --  or an access object denoted by a direct or indirect
                     --  observer (respectively, borrower) of the traversed
                     --  parameter.
                     --
                     --  ??? We could possibly allow case and if expressions
                     --  returning paths rooted at the right variable. TBD when
                     --  we know how to support them in proof.
                     --  ??? Should we move that to marking? Do we need this
                     --  check for flow analysis?

                     if Is_Anonymous_Access_Type (Return_Typ) then
                        if Nkind (Expr) /= N_Null then
                           declare
                              Param : constant Entity_Id :=
                                First_Formal (Subp);
                              Root : Entity_Id := Get_Root_Object (Expr);

                           begin
                              while Root /= Param loop
                                 if Get (Current_Observers, Root) /= Empty then
                                    Root := Get_Root_Object
                                      (Get (Current_Observers, Root));
                                 elsif Get (Current_Borrowers, Root) /= Empty
                                 then
                                    Root := Get_Root_Object
                                      (Get (Current_Borrowers, Root));
                                 else
                                    Error_Msg_NE
                                      ("return value of a traversal function "
                                       & "should be rooted at &", Expr, Param);
                                    Permission_Error := True;
                                    exit;
                                 end if;
                              end loop;
                           end;
                        end if;

                     --  Otherwise, if the return type is deep, we have a move

                     elsif Is_Deep (Return_Typ) then
                        pragma Assert (Is_Path_Expression (Expr));

                        Check_Expression (Expr, Move);

                     else
                        Check_Expression (Expr, Read);
                     end if;

                     if Ekind_In (Subp, E_Procedure, E_Entry)
                       and then not No_Return (Subp)
                     then
                        Return_Parameters (Subp);
                        Return_Globals (Subp);
                     end if;
                  end;
               end if;
            end;

         when N_Extended_Return_Statement =>
            declare
               Subp  : constant Entity_Id :=
                 Return_Applies_To (Return_Statement_Entity (Stmt));
               Decls : constant List_Id := Return_Object_Declarations (Stmt);
               Decl  : constant Node_Id := Last_Non_Pragma (Decls);
               Obj   : constant Entity_Id := Defining_Identifier (Decl);
               Perm  : Perm_Kind;

            begin
               pragma Assert (not Is_Traversal_Function (Subp));

               Check_List (Return_Object_Declarations (Stmt));
               Check_Node (Handled_Statement_Sequence (Stmt));

               if Is_Deep (Etype (Obj)) then
                  declare
                     E_Obj : constant Expr_Or_Ent :=
                       (Is_Ent => True, Ent => Obj, Loc => Decl);
                  begin
                     Perm := Get_Perm (E_Obj);

                     if Perm /= Read_Write then
                        Perm_Error (E_Obj, Read_Write, Perm,
                                    Expl => Get_Expl (E_Obj));
                     end if;
                  end;
               end if;

               if Ekind_In (Subp, E_Procedure, E_Entry)
                 and then not No_Return (Subp)
               then
                  Return_Parameters (Subp);
                  Return_Globals (Subp);
               end if;
            end;

         --  On loop exit, merge the current permission environment with the
         --  accumulator for the given loop.

         when N_Exit_Statement =>
            declare
               Loop_Name         : constant Entity_Id := Loop_Of_Exit (Stmt);
               Saved_Accumulator : constant Perm_Env_Access :=
                 Get (Current_Loops_Accumulators, Loop_Name);
               Environment_Copy  : constant Perm_Env_Access :=
                 new Perm_Env;
            begin
               Copy_Env (Current_Perm_Env, Environment_Copy.all);

               if Saved_Accumulator = null then
                  Set (Current_Loops_Accumulators,
                       Loop_Name, Environment_Copy);
               else
                  Merge_Env (Source => Environment_Copy.all,
                             Target => Saved_Accumulator.all);
                  --  ??? Either free Environment_Copy, or change the type
                  --  of loop accumulators to directly store permission
                  --  environments.
               end if;
            end;

         --  On branches, analyze each branch independently on a fresh copy of
         --  the permission environment, then merge the resulting permission
         --  environments.

         when N_If_Statement =>
            declare
               Saved_Env : Perm_Env;
               New_Env   : Perm_Env;
               --  Accumulator for the different branches

            begin
               Check_Expression (Condition (Stmt), Read);

               --  Save environment

               Copy_Env (Current_Perm_Env, Saved_Env);

               --  THEN branch

               Check_List (Then_Statements (Stmt));
               Move_Env (Current_Perm_Env, New_Env);

               --  ELSIF branches

               declare
                  Branch : Node_Id;
               begin
                  Branch := First (Elsif_Parts (Stmt));
                  while Present (Branch) loop

                     --  Restore current permission environment

                     Copy_Env (Saved_Env, Current_Perm_Env);
                     Check_Expression (Condition (Branch), Read);
                     Check_List (Then_Statements (Branch));

                     --  Merge current permission environment

                     Merge_Env (Source => Current_Perm_Env, Target => New_Env);
                     Next (Branch);
                  end loop;
               end;

               --  ELSE branch

               --  Restore current permission environment

               Copy_Env (Saved_Env, Current_Perm_Env);
               Check_List (Else_Statements (Stmt));

               --  Merge current permission environment

               Merge_Env (Source => Current_Perm_Env, Target => New_Env);

               --  Cleanup

               Move_Env (New_Env, Current_Perm_Env);
               Free_Env (Saved_Env);
            end;

         --  We should ideally ignore the branch after raising an exception,
         --  so that it is not taken into account in merges. For now, just
         --  propagate the current environment.

         when N_Raise_Statement =>
            null;

         when N_Null_Statement =>
            null;

         --  Unsupported constructs in SPARK

         when N_Abort_Statement
            | N_Accept_Statement
            | N_Asynchronous_Select
            | N_Code_Statement
            | N_Conditional_Entry_Call
            | N_Goto_Statement
            | N_Requeue_Statement
            | N_Selective_Accept
            | N_Timed_Entry_Call
         =>
            null;

         --  The following nodes are never generated in GNATprove mode

         when N_Compound_Statement
            | N_Free_Statement
         =>
            raise Program_Error;
      end case;
   end Check_Statement;

   ----------------------------
   -- Found_Permission_Error --
   ----------------------------

   function Found_Permission_Error return Boolean is (Permission_Error);

   --------------
   -- Get_Expl --
   --------------

   function Get_Expl (N : Expr_Or_Ent) return Node_Id is
   begin
      if N.Is_Ent then
         declare
            C : constant Perm_Tree_Access :=
              Get (Current_Perm_Env, Unique_Entity (N.Ent));
         begin
            pragma Assert (C /= null);
            return Explanation (C);
         end;

      --  The expression is a call to a traversal function

      elsif Is_Traversal_Function_Call (N.Expr) then
         return N.Expr;

      --  The expression is directly rooted in an object

      elsif Present (Get_Root_Object (N.Expr, Through_Traversal => False)) then
         declare
            Tree_Or_Perm : constant Perm_Or_Tree := Get_Perm_Or_Tree (N);
         begin
            case Tree_Or_Perm.R is
               when Folded =>
                  return Tree_Or_Perm.Explanation;

               when Unfolded =>
                  pragma Assert (Tree_Or_Perm.Tree_Access /= null);
                  return Explanation (Tree_Or_Perm.Tree_Access);
            end case;
         end;

      --  The expression is a function call, an allocation, or null

      else
         return N.Expr;
      end if;
   end Get_Expl;

   --------------
   -- Get_Perm --
   --------------

   function Get_Perm (N : Expr_Or_Ent) return Perm_Kind is
   begin
      if N.Is_Ent then
         declare
            C : constant Perm_Tree_Access :=
              Get (Current_Perm_Env, Unique_Entity (N.Ent));
         begin
            pragma Assert (C /= null);
            return Permission (C);
         end;

      --  The expression is a call to a traversal function

      elsif Is_Traversal_Function_Call (N.Expr) then
         declare
            Callee : constant Entity_Id := Get_Called_Entity (N.Expr);
         begin
            if Is_Access_Constant (Etype (Callee)) then
               return Read_Only;
            else
               return Read_Write;
            end if;
         end;

      --  The expression is directly rooted in an object

      elsif Present (Get_Root_Object (N.Expr, Through_Traversal => False)) then
         declare
            Tree_Or_Perm : constant Perm_Or_Tree := Get_Perm_Or_Tree (N);
         begin
            case Tree_Or_Perm.R is
               when Folded =>
                  return Tree_Or_Perm.Found_Permission;

               when Unfolded =>
                  pragma Assert (Tree_Or_Perm.Tree_Access /= null);
                  return Permission (Tree_Or_Perm.Tree_Access);
            end case;
         end;

      --  The expression is a function call, an allocation, or null

      else
         return Read_Write;
      end if;
   end Get_Perm;

   ----------------------
   -- Get_Perm_Or_Tree --
   ----------------------

   function Get_Perm_Or_Tree (N : Expr_Or_Ent) return Perm_Or_Tree is

      function Get_Perm_Or_Tree_Ent (E : Entity_Id) return Perm_Or_Tree;
      --  Get permission of the entity E

      --------------------------
      -- Get_Perm_Or_Tree_Ent --
      --------------------------

      function Get_Perm_Or_Tree_Ent (E : Entity_Id) return Perm_Or_Tree is
         C : constant Perm_Tree_Access :=
           Get (Current_Perm_Env, Unique_Entity (E));
      begin
         --  The root object should have been declared and entered into the
         --  current permission environment.

         if C = null then
            pragma Assert
              (Ekind (E) = E_Constant and then not Has_Variable_Input (E));
         end if;

         return (R => Unfolded, Tree_Access => C);
      end Get_Perm_Or_Tree_Ent;

   begin
      if N.Is_Ent then
         return Get_Perm_Or_Tree_Ent (N.Ent);
      end if;

      case Nkind (N.Expr) is

         when N_Expanded_Name
            | N_Identifier
         =>
            return Get_Perm_Or_Tree_Ent (Entity (N.Expr));

         --  For a nonterminal path, we get the permission tree of its
         --  prefix, and then get the subtree associated with the extension,
         --  if unfolded. If folded, we return the permission associated with
         --  children.

         when N_Explicit_Dereference
            | N_Indexed_Component
            | N_Selected_Component
            | N_Slice
         =>
            declare
               C : constant Perm_Or_Tree :=
                 Get_Perm_Or_Tree (+Prefix (N.Expr));
            begin
               case C.R is

                  --  Some earlier prefix was already folded, return the
                  --  permission found.

                  when Folded =>
                     return C;

                  when Unfolded =>
                     case Kind (C.Tree_Access) is

                        --  If the prefix tree is already folded, return the
                        --  children permission.

                        when Entire_Object =>
                           return (R                => Folded,
                                   Found_Permission =>
                                      Children_Permission (C.Tree_Access),
                                   Explanation      =>
                                      Explanation (C.Tree_Access));

                        when Reference =>
                           pragma Assert
                             (Nkind (N.Expr) = N_Explicit_Dereference);
                           return (R           => Unfolded,
                                   Tree_Access => Get_All (C.Tree_Access));

                        when Record_Component =>
                           pragma Assert
                             (Nkind (N.Expr) = N_Selected_Component);
                           declare
                              Comp : constant Entity_Id :=
                                Original_Record_Component
                                  (Entity (Selector_Name (N.Expr)));
                              D : constant Perm_Tree_Access :=
                                Perm_Tree_Maps.Get
                                  (Component (C.Tree_Access), Comp);
                           begin
                              pragma Assert (D /= null);
                              return (R           => Unfolded,
                                      Tree_Access => D);
                           end;

                        when Array_Component =>
                           pragma Assert (Nkind (N.Expr) = N_Indexed_Component
                                            or else
                                          Nkind (N.Expr) = N_Slice);
                           pragma Assert (Get_Elem (C.Tree_Access) /= null);
                           return (R => Unfolded,
                                   Tree_Access => Get_Elem (C.Tree_Access));
                     end case;
               end case;
            end;

         when N_Qualified_Expression
            | N_Type_Conversion
            | N_Unchecked_Type_Conversion
         =>
            return Get_Perm_Or_Tree (+Expression (N.Expr));

         when others =>
            raise Program_Error;
      end case;
   end Get_Perm_Or_Tree;

   -------------------
   -- Get_Perm_Tree --
   -------------------

   function Get_Perm_Tree (N : Expr_Or_Ent) return Perm_Tree_Access is
   begin
      return Set_Perm_Prefixes (N, None, Empty);
   end Get_Perm_Tree;

   ---------
   -- Glb --
   ---------

   function Glb (P1, P2 : Perm_Kind) return Perm_Kind
   is
   begin
      case P1 is
         when No_Access =>
            return No_Access;

         when Read_Only =>
            case P2 is
               when No_Access
                  | Write_Only
               =>
                  return No_Access;

               when Read_Perm =>
                  return Read_Only;
            end case;

         when Write_Only =>
            case P2 is
               when No_Access
                  | Read_Only
               =>
                  return No_Access;

               when Write_Perm =>
                  return Write_Only;
            end case;

         when Read_Write =>
            return P2;
      end case;
   end Glb;

   -------------------------
   -- Has_Array_Component --
   -------------------------

   function Has_Array_Component (Expr : Node_Id) return Boolean is
   begin
      case Nkind (Expr) is
         when N_Expanded_Name
            | N_Identifier
         =>
            return False;

         when N_Explicit_Dereference
            | N_Selected_Component
         =>
            return Has_Array_Component (Prefix (Expr));

         when N_Indexed_Component
            | N_Slice
         =>
            return True;

         when N_Allocator
            | N_Null
            | N_Function_Call
         =>
            return False;

         when N_Qualified_Expression
            | N_Type_Conversion
            | N_Unchecked_Type_Conversion
         =>
            return Has_Array_Component (Expression (Expr));

         when others =>
            raise Program_Error;
      end case;
   end Has_Array_Component;

   --------
   -- Hp --
   --------

   procedure Hp (P : Perm_Env) is
      Elem : Perm_Tree_Maps.Key_Option;

   begin
      Elem := Get_First_Key (P);
      while Elem.Present loop
         Print_Node_Briefly (Elem.K);
         Elem := Get_Next_Key (P);
      end loop;
   end Hp;

   -------------------------
   -- Is_Prefix_Or_Almost --
   -------------------------

   function Is_Prefix_Or_Almost
     (Pref : Node_Id;
      Expr : Expr_Or_Ent) return Boolean
   is

      type Expr_Array is array (Positive range <>) of Node_Or_Entity_Id;
      --  Sequence of expressions that make up a path. The first element is
      --  always an entity when the path has a root.

      function Get_Expr_Array (Expr : Node_Id) return Expr_Array;
      pragma Precondition (Is_Path_Expression (Expr));
      --  Return the sequence of expressions that make up a path

      --------------------
      -- Get_Expr_Array --
      --------------------

      function Get_Expr_Array (Expr : Node_Id) return Expr_Array is
      begin
         case Nkind (Expr) is
            when N_Expanded_Name
               | N_Identifier
            =>
               return Expr_Array'(1 => Entity (Expr));

            when N_Explicit_Dereference
               | N_Indexed_Component
               | N_Selected_Component
               | N_Slice
            =>
               return Get_Expr_Array (Prefix (Expr)) & Expr;

            when N_Qualified_Expression
               | N_Type_Conversion
               | N_Unchecked_Type_Conversion
            =>
               return Get_Expr_Array (Expression (Expr));

            when others =>
               raise Program_Error;
         end case;
      end Get_Expr_Array;

      --  Local variables

      Prefix_Path : constant Expr_Array := Get_Expr_Array (Pref);
      Expr_Path   : constant Expr_Array :=
        (if Expr.Is_Ent then (1 => Expr.Ent)
         else Get_Expr_Array (Get_Observed_Or_Borrowed_Expr (Expr.Expr)));

      Prefix_Root : constant Entity_Id := Prefix_Path (1);
      Expr_Root   : constant Entity_Id := Expr_Path (1);

      Common_Len  : constant Positive :=
        Positive'Min (Prefix_Path'Length, Expr_Path'Length);

   --  Start of processing for Is_Prefix_Or_Almost

   begin
      if Prefix_Root /= Expr_Root then
         return False;
      end if;

      for J in 2 .. Common_Len loop
         declare
            Prefix_Elt : constant Node_Id := Prefix_Path (J);
            Expr_Elt   : constant Node_Id := Expr_Path (J);
         begin
            case Nkind (Prefix_Elt) is
               when N_Explicit_Dereference =>
                  if Nkind (Expr_Elt) /= N_Explicit_Dereference then
                     return False;
                  end if;

               when N_Selected_Component =>
                  if Nkind (Expr_Elt) /= N_Selected_Component
                    or else Original_Record_Component
                              (Entity (Selector_Name (Prefix_Elt)))
                         /= Original_Record_Component
                              (Entity (Selector_Name (Expr_Elt)))
                  then
                     return False;
                  end if;

               when N_Indexed_Component
                  | N_Slice
               =>
                  if not Nkind_In (Expr_Elt, N_Indexed_Component, N_Slice) then
                     return False;
                  end if;

               when others =>
                  raise Program_Error;
            end case;
         end;
      end loop;

      --  If the expression path is longer than the prefix one, then at this
      --  point the prefix property holds.

      if Expr_Path'Length > Prefix_Path'Length then
         return True;

      --  Otherwise check if none of the remaining path elements in the
      --  candidate prefix involve a dereference.

      else
         for J in Common_Len + 1 .. Prefix_Path'Length loop
            if Nkind (Prefix_Path (J)) = N_Explicit_Dereference then
               return False;
            end if;
         end loop;

         return True;
      end if;
   end Is_Prefix_Or_Almost;

   ------------------
   -- Is_Read_Only --
   ------------------

   function Is_Read_Only (E : Entity_Id) return Boolean is
      Ty : constant Entity_Id := Etype (E);
   begin
      case Ekind (E) is
         when E_Constant | E_In_Parameter =>
            return not Is_Access_Type (Ty)
              or else Is_Access_Constant (Ty);
         when E_Variable =>
            return Is_Access_Type (Ty)
              and then Is_Access_Constant (Ty);
         when others =>
            return False;
      end case;
   end Is_Read_Only;

   ------------------
   -- Loop_Of_Exit --
   ------------------

   function Loop_Of_Exit (N : Node_Id) return Entity_Id is
      Nam : Node_Id := Name (N);
      Stmt : Node_Id := N;
   begin
      if No (Nam) then
         while Present (Stmt) loop
            Stmt := Parent (Stmt);
            if Nkind (Stmt) = N_Loop_Statement then
               Nam := Identifier (Stmt);
               exit;
            end if;
         end loop;
      end if;
      return Entity (Nam);
   end Loop_Of_Exit;

   ---------
   -- Lub --
   ---------

   function Lub (P1, P2 : Perm_Kind) return Perm_Kind is
   begin
      case P1 is
         when No_Access =>
            return P2;

         when Read_Only =>
            case P2 is
               when No_Access
                  | Read_Only
               =>
                  return Read_Only;

               when Write_Perm =>
                  return Read_Write;
            end case;

         when Write_Only =>
            case P2 is
               when No_Access
                  | Write_Only
               =>
                  return Write_Only;

               when Read_Perm =>
                  return Read_Write;
            end case;

         when Read_Write =>
            return Read_Write;
      end case;
   end Lub;

   ---------------
   -- Merge_Env --
   ---------------

   procedure Merge_Env (Source : in out Perm_Env; Target : in out Perm_Env) is

      --  Local subprograms

      procedure Apply_Glb_Tree
        (A : Perm_Tree_Access;
         P : Perm_Kind);

      procedure Merge_Trees
        (Target : Perm_Tree_Access;
         Source : Perm_Tree_Access);

      --------------------
      -- Apply_Glb_Tree --
      --------------------

      procedure Apply_Glb_Tree
        (A : Perm_Tree_Access;
         P : Perm_Kind)
      is
      begin
         A.all.Tree.Permission := Glb (Permission (A), P);

         case Kind (A) is
            when Entire_Object =>
               A.all.Tree.Children_Permission :=
                 Glb (Children_Permission (A), P);

            when Reference =>
               Apply_Glb_Tree (Get_All (A), P);

            when Array_Component =>
               Apply_Glb_Tree (Get_Elem (A), P);

            when Record_Component =>
               declare
                  Comp : Perm_Tree_Access;
               begin
                  Comp := Perm_Tree_Maps.Get_First (Component (A));
                  while Comp /= null loop
                     Apply_Glb_Tree (Comp, P);
                     Comp := Perm_Tree_Maps.Get_Next (Component (A));
                  end loop;
               end;
         end case;
      end Apply_Glb_Tree;

      -----------------
      -- Merge_Trees --
      -----------------

      procedure Merge_Trees
        (Target : Perm_Tree_Access;
         Source : Perm_Tree_Access)
      is
         Perm : constant Perm_Kind :=
           Glb (Permission (Target), Permission (Source));

      begin
         pragma Assert (Is_Node_Deep (Target) = Is_Node_Deep (Source));
         Target.all.Tree.Permission := Perm;

         case Kind (Target) is
            when Entire_Object =>
               declare
                  Child_Perm : constant Perm_Kind :=
                    Children_Permission (Target);

               begin
                  case Kind (Source) is
                  when Entire_Object =>
                     Target.all.Tree.Children_Permission :=
                       Glb (Child_Perm, Children_Permission (Source));

                  when Reference =>
                     Copy_Tree (Source, Target);
                     Target.all.Tree.Permission := Perm;
                     Apply_Glb_Tree (Get_All (Target), Child_Perm);

                  when Array_Component =>
                     Copy_Tree (Source, Target);
                     Target.all.Tree.Permission := Perm;
                     Apply_Glb_Tree (Get_Elem (Target), Child_Perm);

                  when Record_Component =>
                     Copy_Tree (Source, Target);
                     Target.all.Tree.Permission := Perm;
                     declare
                        Comp : Perm_Tree_Access;

                     begin
                        Comp :=
                          Perm_Tree_Maps.Get_First (Component (Target));
                        while Comp /= null loop
                           --  Apply glb tree on every component subtree

                           Apply_Glb_Tree (Comp, Child_Perm);
                           Comp := Perm_Tree_Maps.Get_Next
                             (Component (Target));
                        end loop;
                     end;
                  end case;
               end;

            when Reference =>
               case Kind (Source) is
               when Entire_Object =>
                  Apply_Glb_Tree (Get_All (Target),
                                  Children_Permission (Source));

               when Reference =>
                  Merge_Trees (Get_All (Target), Get_All (Source));

               when others =>
                  raise Program_Error;

               end case;

            when Array_Component =>
               case Kind (Source) is
               when Entire_Object =>
                  Apply_Glb_Tree (Get_Elem (Target),
                                  Children_Permission (Source));

               when Array_Component =>
                  Merge_Trees (Get_Elem (Target), Get_Elem (Source));

               when others =>
                  raise Program_Error;

               end case;

            when Record_Component =>
               case Kind (Source) is
               when Entire_Object =>
                  declare
                     Child_Perm : constant Perm_Kind :=
                       Children_Permission (Source);

                     Comp : Perm_Tree_Access;

                  begin
                     Comp := Perm_Tree_Maps.Get_First
                       (Component (Target));
                     while Comp /= null loop
                        --  Apply glb tree on every component subtree

                        Apply_Glb_Tree (Comp, Child_Perm);
                        Comp :=
                          Perm_Tree_Maps.Get_Next (Component (Target));
                     end loop;
                  end;

               when Record_Component =>
                  declare
                     Key_Source : Perm_Tree_Maps.Key_Option;
                     CompTarget : Perm_Tree_Access;
                     CompSource : Perm_Tree_Access;

                  begin
                     Key_Source := Perm_Tree_Maps.Get_First_Key
                       (Component (Source));

                     while Key_Source.Present loop
                        CompSource := Perm_Tree_Maps.Get
                          (Component (Source), Key_Source.K);
                        CompTarget := Perm_Tree_Maps.Get
                          (Component (Target), Key_Source.K);

                        pragma Assert (CompSource /= null);
                        Merge_Trees (CompTarget, CompSource);

                        Key_Source := Perm_Tree_Maps.Get_Next_Key
                          (Component (Source));
                     end loop;
                  end;

               when others =>
                  raise Program_Error;
               end case;
         end case;
      end Merge_Trees;

      --  Local variables

      CompTarget : Perm_Tree_Access;
      CompSource : Perm_Tree_Access;
      KeyTarget : Perm_Tree_Maps.Key_Option;

   --  Start of processing for Merge_Env

   begin
      KeyTarget := Get_First_Key (Target);
      --  Iterate over every tree of the environment in the target, and merge
      --  it with the source if there is such a similar one that exists. If
      --  there is none, then skip.
      while KeyTarget.Present loop

         CompSource := Get (Source, KeyTarget.K);
         CompTarget := Get (Target, KeyTarget.K);

         pragma Assert (CompTarget /= null);

         if CompSource /= null then
            Merge_Trees (CompTarget, CompSource);
            Remove (Source, KeyTarget.K);
         end if;

         KeyTarget := Get_Next_Key (Target);
      end loop;

      --  Iterate over every tree of the environment of the source. And merge
      --  again. If there is not any tree of the target then just copy the tree
      --  from source to target.
      declare
         KeySource : Perm_Tree_Maps.Key_Option;
      begin
         KeySource := Get_First_Key (Source);
         while KeySource.Present loop

            CompSource := Get (Source, KeySource.K);
            CompTarget := Get (Target, KeySource.K);

            if CompTarget = null then
               CompTarget := new Perm_Tree_Wrapper'(CompSource.all);
               Copy_Tree (CompSource, CompTarget);
               Set (Target, KeySource.K, CompTarget);
            else
               Merge_Trees (CompTarget, CompSource);
            end if;

            KeySource := Get_Next_Key (Source);
         end loop;
      end;

      Free_Env (Source);
   end Merge_Env;

   ----------------
   -- Perm_Error --
   ----------------

   procedure Perm_Error
     (N              : Expr_Or_Ent;
      Perm           : Perm_Kind;
      Found_Perm     : Perm_Kind;
      Expl           : Node_Id;
      Forbidden_Perm : Boolean := False)
   is
      procedure Set_Root_Object
        (Path  : Node_Id;
         Obj   : out Entity_Id;
         Deref : out Boolean);
      --  Set the root object Obj, and whether the path contains a dereference,
      --  from a path Path.

      ---------------------
      -- Set_Root_Object --
      ---------------------

      procedure Set_Root_Object
        (Path  : Node_Id;
         Obj   : out Entity_Id;
         Deref : out Boolean)
      is
      begin
         case Nkind (Path) is
            when N_Identifier
               | N_Expanded_Name
            =>
               Obj := Entity (Path);
               Deref := False;

            when N_Type_Conversion
               | N_Unchecked_Type_Conversion
               | N_Qualified_Expression
            =>
               Set_Root_Object (Expression (Path), Obj, Deref);

            when N_Indexed_Component
               | N_Selected_Component
               | N_Slice
            =>
               Set_Root_Object (Prefix (Path), Obj, Deref);

            when N_Explicit_Dereference =>
               Set_Root_Object (Prefix (Path), Obj, Deref);
               Deref := True;

            when others =>
               raise Program_Error;
         end case;
      end Set_Root_Object;
      --  Local variables

      Root     : Entity_Id;
      Loc      : constant Node_Id :=
        (if N.Is_Ent then N.Loc else N.Expr);
      Is_Deref : Boolean;

   --  Start of processing for Perm_Error

   begin
      if N.Is_Ent then
         Is_Deref := False;
         Root := N.Ent;
      else
         Set_Root_Object (N.Expr, Root, Is_Deref);
      end if;

      if Is_Deref then
         Error_Msg_NE
           ("insufficient permission on dereference from &", Loc, Root);
      else
         Error_Msg_NE ("insufficient permission for &", Loc, Root);
      end if;

      Permission_Error := True;

      Perm_Mismatch (Loc, Perm, Found_Perm, Expl, Forbidden_Perm);
   end Perm_Error;

   -------------------------------
   -- Perm_Error_Subprogram_End --
   -------------------------------

   procedure Perm_Error_Subprogram_End
     (E          : Entity_Id;
      Subp       : Entity_Id;
      Perm       : Perm_Kind;
      Found_Perm : Perm_Kind;
      Expl       : Node_Id)
   is
   begin
      Error_Msg_Node_2 := Subp;
      Error_Msg_NE ("insufficient permission for & when returning from &",
                    Subp, E);
      Permission_Error := True;
      Perm_Mismatch (Subp, Perm, Found_Perm, Expl);
   end Perm_Error_Subprogram_End;

   ------------------
   -- Process_Path --
   ------------------

   procedure Process_Path (Expr : Expr_Or_Ent; Mode : Checking_Mode) is
      Expr_Type : constant Entity_Id :=
        (if Expr.Is_Ent then Etype (Expr.Ent)
         else Etype (Expr.Expr));
      Root      : Entity_Id :=
        (if Expr.Is_Ent then Expr.Ent
         else Get_Root_Object (Expr.Expr));
      Loc       : constant Node_Id :=
        (if Expr.Is_Ent then Expr.Loc else Expr.Expr);
      Perm      : Perm_Kind_Option;
      Expl      : Node_Id;

   begin
      --  Nothing to do if the root type is not deep, or the path is not rooted
      --  in an object.

      if not Present (Root)
        or else not Is_Object (Root)
        or else not Is_Deep (Etype (Root))
      then
         return;
      end if;

      --  Identify the root type for the path

      Root := Unique_Entity (Root);

      if Get (Current_Perm_Env, Root) = null then

         --  If the root object is not in the current environment, then it must
         --  be a constant without variable input. It can only be read.
         --  ??? shouldn't a new be considered as having variable inputs?

         pragma Assert
           (Ekind (Root) = E_Constant and then not Has_Variable_Input (Root));

         Perm := Read_Only;
         Expl := Root;
      else
         Perm := Get_Perm (Expr);
         Expl := Get_Expl (Expr);
      end if;

      --  Check permissions

      case Mode is

         when Read =>
            --  Check path is readable

            if Perm not in Read_Perm then
               Perm_Error (Expr, Read_Only, Perm, Expl => Expl);
               return;
            end if;

         when Move =>

            --  Forbidden on deep path during elaboration, otherwise no
            --  checking needed.

            if Inside_Elaboration then
               if Is_Deep (Expr_Type)
                 and then not Inside_Procedure_Call
                 and then Present (Root)
               then
                  Error_Msg_N ("illegal move during elaboration", Loc);
                  Permission_Error := True;
               end if;

               return;
            end if;

            --  For deep path, check RW permission, otherwise R permission

            if not Is_Deep (Expr_Type) then
               if Perm not in Read_Perm then
                  Perm_Error (Expr, Read_Only, Perm, Expl => Expl);
               end if;
               return;
            end if;

            --  SPARK RM 3.10(1): At the point of a move operation the state of
            --  the source object (if any) shall be Unrestricted.

            if Perm /= Read_Write then
               Perm_Error (Expr, Read_Write, Perm, Expl => Expl);
               return;
            end if;

         when Assign =>
            --  For assignment, check W permission

            if Perm not in Write_Perm then
               Perm_Error (Expr, Write_Only, Perm, Expl => Expl);
               return;
            end if;

         when Borrow =>

            --  Forbidden during elaboration, an error is already issued in
            --  Check_Declaration, just return.

            if Inside_Elaboration then
               return;
            end if;

            --  For borrowing, check RW permission

            if Perm /= Read_Write then
               Perm_Error (Expr, Read_Write, Perm, Expl => Expl);
               return;
            end if;

         when Observe =>

            --  Forbidden during elaboration, an error is already issued in
            --  Check_Declaration, just return.

            if Inside_Elaboration then
               return;
            end if;

            --  For observing, check R permission

            if Perm not in Read_Perm then
               Perm_Error (Expr, Read_Only, Perm, Expl => Expl);
               return;
            end if;
      end case;

      --  Check path was not borrowed

      Check_Not_Borrowed (Expr, Root);

      --  For modes that require W permission, check path was not observed

      case Mode is
         when Read | Observe =>
            null;
         when Assign | Move | Borrow =>
            Check_Not_Observed (Expr, Root);
      end case;

      --  Do not update permission environment when handling calls

      if Inside_Procedure_Call then
         return;
      end if;

      --  Update the permissions

      case Mode is

         when Read =>
            null;

         when Move =>

            --  SPARK RM 3.10(1): After a move operation, the state of the
            --  source object (if any) becomes Moved.

            if Present (Root) then
               declare
                  Tree : constant Perm_Tree_Access :=
                    Set_Perm_Prefixes (Expr, Write_Only, Expl => Loc);
               begin
                  pragma Assert (Tree /= null);
                  Set_Perm_Extensions_Move (Tree, Expr_Type, Expl => Loc);
               end;
            end if;

         when Assign =>

            --  If there is no root object, or the tree has an array component,
            --  then the permissions do not get modified by the assignment.

            if No (Root)
              or else
                (not Expr.Is_Ent and then Has_Array_Component (Expr.Expr))
            then
               return;
            end if;

            --  Set permission RW for the path and its extensions

            declare
               Tree : constant Perm_Tree_Access := Get_Perm_Tree (Expr);
            begin
               Tree.all.Tree.Permission := Read_Write;
               Set_Perm_Extensions (Tree, Read_Write, Expl => Loc);

               --  Normalize the permission tree

               Set_Perm_Prefixes_Assign (Expr);
            end;

         --  Borrowing and observing of paths is handled by the variables
         --  Current_Borrowers and Current_Observers.

         when Borrow | Observe =>
            null;
      end case;
   end Process_Path;

   --------------------
   -- Return_Globals --
   --------------------

   procedure Return_Globals (Subp : Entity_Id) is

      procedure Return_Global
        (Expr       : Expr_Or_Ent;
         Typ        : Entity_Id;
         Kind       : Formal_Kind;
         Subp       : Entity_Id;
         Global_Var : Boolean);
      --  Proxy procedure to return globals, to adjust for the type of first
      --  parameter expected by Return_Parameter_Or_Global.

      -------------------
      -- Return_Global --
      -------------------

      procedure Return_Global
        (Expr       : Expr_Or_Ent;
         Typ        : Entity_Id;
         Kind       : Formal_Kind;
         Subp       : Entity_Id;
         Global_Var : Boolean)
      is
      begin
         Return_Parameter_Or_Global
           (Id         => Expr.Ent,
            Typ        => Typ,
            Kind       => Kind,
            Subp       => Subp,
            Global_Var => Global_Var);
      end Return_Global;

      procedure Return_Globals_Inst is new Handle_Globals (Return_Global);

   --  Start of processing for Return_Globals

   begin
      Return_Globals_Inst (Subp, Empty);
   end Return_Globals;

   --------------------------------
   -- Return_Parameter_Or_Global --
   --------------------------------

   procedure Return_Parameter_Or_Global
     (Id         : Entity_Id;
      Typ        : Entity_Id;
      Kind       : Formal_Kind;
      Subp       : Entity_Id;
      Global_Var : Boolean)
   is
   begin
      --  Shallow parameters and globals need not be considered

      if not Is_Deep (Typ) then
         return;

      elsif Kind = E_In_Parameter then

         --  If Id is a read-only global variable, it cannot have been moved.
         --  Otherwise, the variable was declared with the permission from its
         --  declaration, and not the one from the global contract to
         --  have better error messages in the case of generated globals (see
         --  Set_Parameter_Or_Global). So we need to check its permission here.

         if Global_Var then
            if Is_Read_Only (Id) then
               return;
            end if;

         --  Anonymous access to constant is an observe

         elsif Is_Anonymous_Access_Type (Typ)
           and then Is_Access_Constant (Typ)
         then
            return;

         --  Deep types other than access types define an observe

         elsif not Is_Access_Type (Typ) then
            return;
         end if;
      end if;

      --  All other parameters and globals should return with mode RW to the
      --  caller.

      declare
         Tree : constant Perm_Tree_Access := Get (Current_Perm_Env, Id);
      begin
         if Permission (Tree) /= Read_Write then
            Perm_Error_Subprogram_End
              (E          => Id,
               Subp       => Subp,
               Perm       => Read_Write,
               Found_Perm => Permission (Tree),
               Expl       => Explanation (Tree));
         end if;
      end;
   end Return_Parameter_Or_Global;

   -----------------------
   -- Return_Parameters --
   -----------------------

   procedure Return_Parameters (Subp : Entity_Id) is
      Formal : Entity_Id;
   begin
      Formal := First_Formal (Subp);
      while Present (Formal) loop
         Return_Parameter_Or_Global
           (Id         => Formal,
            Typ        => Retysp (Etype (Formal)),
            Kind       => Ekind (Formal),
            Subp       => Subp,
            Global_Var => False);
         Next_Formal (Formal);
      end loop;
   end Return_Parameters;

   -------------------------
   -- Set_Perm_Extensions --
   -------------------------

   procedure Set_Perm_Extensions
     (T    : Perm_Tree_Access;
      P    : Perm_Kind;
      Expl : Node_Id) is

      procedure Free_Perm_Tree_Children (T : Perm_Tree_Access);
      --  Free the permission tree of children if any, prio to replacing T

      -----------------------------
      -- Free_Perm_Tree_Children --
      -----------------------------

      procedure Free_Perm_Tree_Children (T : Perm_Tree_Access) is
      begin
         case Kind (T) is
            when Entire_Object =>
               null;

            when Reference =>
               Free_Tree (T.all.Tree.Get_All);

            when Array_Component =>
               Free_Tree (T.all.Tree.Get_Elem);

            when Record_Component =>
               declare
                  Hashtbl : Perm_Tree_Maps.Instance := Component (T);
                  Comp    : Perm_Tree_Access;

               begin
                  Comp := Perm_Tree_Maps.Get_First (Hashtbl);
                  while Comp /= null loop
                     Free_Tree (Comp);
                     Comp := Perm_Tree_Maps.Get_Next (Hashtbl);
                  end loop;

                  Perm_Tree_Maps.Reset (Hashtbl);
               end;
         end case;
      end Free_Perm_Tree_Children;

   --  Start of processing for Set_Perm_Extensions

   begin
      Free_Perm_Tree_Children (T);
      T.all.Tree := Perm_Tree'(Kind                => Entire_Object,
                               Is_Node_Deep        => Is_Node_Deep (T),
                               Explanation         => Expl,
                               Permission          => Permission (T),
                               Children_Permission => P);
   end Set_Perm_Extensions;

   ------------------------------
   -- Set_Perm_Extensions_Move --
   ------------------------------

   procedure Set_Perm_Extensions_Move
     (T    : Perm_Tree_Access;
      E    : Entity_Id;
      Expl : Node_Id)
   is
      Check_Ty : constant Entity_Id := Retysp (E);
   begin
      --  Shallow extensions are set to RW

      if not Is_Node_Deep (T) then
         Set_Perm_Extensions (T, Read_Write, Expl => Expl);
         return;
      end if;

      --  Deep extensions are set to W before .all and NO afterwards

      T.all.Tree.Permission := Write_Only;

      case T.all.Tree.Kind is

         --  For a folded tree of composite type, unfold the tree for better
         --  precision.

         when Entire_Object =>
            case Ekind (Check_Ty) is
               when E_Array_Type
                  | E_Array_Subtype
               =>
                  declare
                     C : constant Perm_Tree_Access :=
                       new Perm_Tree_Wrapper'
                         (Tree =>
                            (Kind                => Entire_Object,
                             Is_Node_Deep        => Is_Node_Deep (T),
                             Explanation         => Expl,
                             Permission          => Read_Write,
                             Children_Permission => Read_Write));
                  begin
                     Set_Perm_Extensions_Move
                       (C, Component_Type (Check_Ty), Expl);
                     T.all.Tree := (Kind         => Array_Component,
                                    Is_Node_Deep => Is_Node_Deep (T),
                                    Explanation  => Expl,
                                    Permission   => Write_Only,
                                    Get_Elem     => C);
                  end;

               when Record_Kind =>
                  declare
                     C       : Perm_Tree_Access;
                     Comp    : Entity_Id;
                     Hashtbl : Perm_Tree_Maps.Instance;

                  begin
                     Comp := First_Component_Or_Discriminant (Check_Ty);
                     while Present (Comp) loop

                        --  Unfold components which are visible in SPARK

                        if Component_Is_Visible_In_SPARK (Comp) then
                           C := new Perm_Tree_Wrapper'
                             (Tree =>
                                (Kind                => Entire_Object,
                                 Is_Node_Deep        => Is_Deep (Etype (Comp)),
                                 Explanation         => Expl,
                                 Permission          => Read_Write,
                                 Children_Permission => Read_Write));
                           Set_Perm_Extensions_Move (C, Etype (Comp), Expl);

                        --  Hidden components are never deep

                        else
                           C := new Perm_Tree_Wrapper'
                             (Tree =>
                                (Kind                => Entire_Object,
                                 Is_Node_Deep        => False,
                                 Explanation         => Expl,
                                 Permission          => Read_Write,
                                 Children_Permission => Read_Write));
                           Set_Perm_Extensions (C, Read_Write, Expl => Expl);
                        end if;

                        Perm_Tree_Maps.Set
                          (Hashtbl, Original_Record_Component (Comp), C);
                        Next_Component_Or_Discriminant (Comp);
                     end loop;

                     T.all.Tree :=
                       (Kind             => Record_Component,
                        Is_Node_Deep     => Is_Node_Deep (T),
                        Explanation      => Expl,
                        Permission       => Write_Only,
                        Component        => Hashtbl);
                  end;

               --  Otherwise, extensions are set to NO

               when others =>
                  Set_Perm_Extensions (T, No_Access, Expl);
            end case;

         when Reference =>
            Set_Perm_Extensions (T, No_Access, Expl);

         when Array_Component =>
            Set_Perm_Extensions_Move
              (Get_Elem (T), Component_Type (Check_Ty), Expl);

         when Record_Component =>
            declare
               C    : Perm_Tree_Access;
               Comp : Entity_Id;

            begin
               Comp := First_Component_Or_Discriminant (Check_Ty);
               while Present (Comp) loop
                  C := Perm_Tree_Maps.Get
                    (Component (T), Original_Record_Component (Comp));
                  pragma Assert (C /= null);

                  --  Move visible components

                  if Component_Is_Visible_In_SPARK (Comp) then
                     Set_Perm_Extensions_Move (C, Etype (Comp), Expl);

                  --  Hidden components are never deep

                  else
                     Set_Perm_Extensions (C, Read_Write, Expl => Expl);
                  end if;

                  Next_Component_Or_Discriminant (Comp);
               end loop;
            end;
      end case;
   end Set_Perm_Extensions_Move;

   -----------------------
   -- Set_Perm_Prefixes --
   -----------------------

   function Set_Perm_Prefixes
     (N    : Expr_Or_Ent;
      Perm : Perm_Kind_Option;
      Expl : Node_Id) return Perm_Tree_Access
   is

      function Set_Perm_Prefixes
        (N    : Entity_Id;
         Perm : Perm_Kind_Option) return Perm_Tree_Access;
      --  Set permission for an entity

      -----------------------
      -- Set_Perm_Prefixes --
      -----------------------

      function Set_Perm_Prefixes
        (N    : Entity_Id;
         Perm : Perm_Kind_Option) return Perm_Tree_Access
      is
         E : constant Entity_Id := Unique_Entity (N);
         C : constant Perm_Tree_Access := Get (Current_Perm_Env, E);
         pragma Assert (C /= null);

      begin
         if Perm /= None then
            C.all.Tree.Permission := Glb (Perm, Permission (C));
         end if;

         return C;
      end Set_Perm_Prefixes;

   begin
      if N.Is_Ent then
         return Set_Perm_Prefixes (N.Ent, Perm);
      end if;

      case Nkind (N.Expr) is
         when N_Expanded_Name
            | N_Identifier
         =>
            return Set_Perm_Prefixes (Entity (N.Expr), Perm);

         --  For a nonterminal path, we set the permission tree of its prefix,
         --  and then we extract from the returned pointer the subtree and
         --  assign an adequate permission to it, if unfolded. If folded,
         --  we unroll the tree one level.

         when N_Explicit_Dereference =>
            declare
               C : constant Perm_Tree_Access :=
                 Set_Perm_Prefixes (+Prefix (N.Expr), Perm, Expl);
               pragma Assert (C /= null);
               pragma Assert (Kind (C) = Entire_Object
                              or else Kind (C) = Reference);
            begin
               --  The tree is already unfolded. Replace the permission of the
               --  dereference.

               if Kind (C) = Reference then
                  declare
                     D : constant Perm_Tree_Access := Get_All (C);
                     pragma Assert (D /= null);

                  begin
                     if Perm /= None then
                        D.all.Tree.Permission := Glb (Perm, Permission (D));
                     end if;

                     return D;
                  end;

               --  The tree is folded. Expand it.

               else
                  declare
                     pragma Assert (Kind (C) = Entire_Object);

                     Child_P : constant Perm_Kind := Children_Permission (C);
                     D : constant Perm_Tree_Access :=
                       new Perm_Tree_Wrapper'
                         (Tree =>
                            (Kind                => Entire_Object,
                             Is_Node_Deep        => Is_Deep (Etype (N.Expr)),
                             Explanation         => Expl,
                             Permission          => Child_P,
                             Children_Permission => Child_P));
                  begin
                     if Perm /= None then
                        D.all.Tree.Permission := Perm;
                     end if;

                     C.all.Tree := (Kind         => Reference,
                                    Is_Node_Deep => Is_Node_Deep (C),
                                    Explanation  => Expl,
                                    Permission   => Permission (C),
                                    Get_All      => D);
                     return D;
                  end;
               end if;
            end;

         when N_Selected_Component =>
            declare
               C : constant Perm_Tree_Access :=
                 Set_Perm_Prefixes (+Prefix (N.Expr), Perm, Expl);
               pragma Assert (C /= null);
               pragma Assert (Kind (C) = Entire_Object
                              or else Kind (C) = Record_Component);
            begin
               --  The tree is already unfolded. Replace the permission of the
               --  component.

               if Kind (C) = Record_Component then
                  declare
                     Comp : constant Entity_Id :=
                       Original_Record_Component
                         (Entity (Selector_Name (N.Expr)));
                     D : constant Perm_Tree_Access :=
                       Perm_Tree_Maps.Get (Component (C), Comp);
                     pragma Assert (D /= null);

                  begin
                     if Perm /= None then
                        D.all.Tree.Permission := Glb (Perm, Permission (D));
                     end if;

                     return D;
                  end;

               --  The tree is folded. Expand it.

               else
                  declare
                     pragma Assert (Kind (C) = Entire_Object);

                     D       : Perm_Tree_Access;
                     D_This  : Perm_Tree_Access;
                     Comp    : Node_Id;
                     P       : Perm_Kind;
                     Child_P : constant Perm_Kind := Children_Permission (C);
                     Hashtbl : Perm_Tree_Maps.Instance;
                     --  Create an empty hash table

                  begin
                     Comp :=
                       First_Component_Or_Discriminant
                         (Retysp (Etype (Prefix (N.Expr))));

                     while Present (Comp) loop
                        if Perm /= None
                          and then Original_Record_Component (Comp) =
                          Original_Record_Component
                            (Entity (Selector_Name (N.Expr)))
                        then
                           P := Perm;
                        else
                           P := Child_P;
                        end if;

                        D := new Perm_Tree_Wrapper'
                          (Tree =>
                             (Kind                => Entire_Object,
                              Is_Node_Deep        =>
                                --  Hidden components are never deep
                                Component_Is_Visible_In_SPARK (Comp)
                                  and then Is_Deep (Etype (Comp)),
                              Explanation         => Expl,
                              Permission          => P,
                              Children_Permission => Child_P));
                        Perm_Tree_Maps.Set
                          (Hashtbl, Original_Record_Component (Comp), D);

                        --  Store the tree to return for this component

                        if Original_Record_Component (Comp) =
                          Original_Record_Component
                            (Entity (Selector_Name (N.Expr)))
                        then
                           D_This := D;
                        end if;

                        Next_Component_Or_Discriminant (Comp);
                     end loop;

                     C.all.Tree := (Kind         => Record_Component,
                                    Is_Node_Deep => Is_Node_Deep (C),
                                    Explanation  => Expl,
                                    Permission   => Permission (C),
                                    Component    => Hashtbl);
                     return D_This;
                  end;
               end if;
            end;

         when N_Indexed_Component
            | N_Slice
         =>
            declare
               C : constant Perm_Tree_Access :=
                 Set_Perm_Prefixes (+Prefix (N.Expr), Perm, Expl);
               pragma Assert (C /= null);
               pragma Assert (Kind (C) = Entire_Object
                              or else Kind (C) = Array_Component);
            begin
               --  The tree is already unfolded. Replace the permission of the
               --  component.

               if Kind (C) = Array_Component then
                  declare
                     D : constant Perm_Tree_Access := Get_Elem (C);
                     pragma Assert (D /= null);

                  begin
                     if Perm /= None then
                        D.all.Tree.Permission := Glb (Perm, Permission (D));
                     end if;

                     return D;
                  end;

               --  The tree is folded. Expand it.

               else
                  declare
                     pragma Assert (Kind (C) = Entire_Object);

                     Child_P : constant Perm_Kind := Children_Permission (C);
                     D : constant Perm_Tree_Access :=
                       new Perm_Tree_Wrapper'
                         (Tree =>
                            (Kind                => Entire_Object,
                             Is_Node_Deep        => Is_Node_Deep (C),
                             Explanation         => Expl,
                             Permission          => Child_P,
                             Children_Permission => Child_P));
                  begin
                     if Perm /= None then
                        D.all.Tree.Permission := Perm;
                     end if;

                     C.all.Tree := (Kind         => Array_Component,
                                    Is_Node_Deep => Is_Node_Deep (C),
                                    Explanation  => Expl,
                                    Permission   => Permission (C),
                                    Get_Elem     => D);
                     return D;
                  end;
               end if;
            end;

         when N_Qualified_Expression
            | N_Type_Conversion
            | N_Unchecked_Type_Conversion
         =>
            return Set_Perm_Prefixes (+Expression (N.Expr), Perm, Expl);

         when others =>
            raise Program_Error;
      end case;
   end Set_Perm_Prefixes;

   ------------------------------
   -- Set_Perm_Prefixes_Assign --
   ------------------------------

   procedure Set_Perm_Prefixes_Assign (N : Expr_Or_Ent) is
      C : constant Perm_Tree_Access := Get_Perm_Tree (N);

   begin
      case Kind (C) is
         when Entire_Object =>
            pragma Assert (Children_Permission (C) = Read_Write);
            C.all.Tree.Permission := Read_Write;

         when Reference =>
            C.all.Tree.Permission :=
              Lub (Permission (C), Permission (Get_All (C)));

         when Array_Component =>
            null;

         when Record_Component =>
            declare
               Comp : Perm_Tree_Access;
               Perm : Perm_Kind := Read_Write;

            begin
               --  We take the Glb of all the descendants, and then update the
               --  permission of the node with it.

               Comp := Perm_Tree_Maps.Get_First (Component (C));
               while Comp /= null loop
                  Perm := Glb (Perm, Permission (Comp));
                  Comp := Perm_Tree_Maps.Get_Next (Component (C));
               end loop;

               C.all.Tree.Permission := Lub (Permission (C), Perm);
            end;
      end case;

      if not N.Is_Ent then
         case Nkind (N.Expr) is

            --  Base identifier end recursion

         when N_Expanded_Name
            | N_Identifier
            =>
            null;

         when N_Explicit_Dereference
            | N_Indexed_Component
            | N_Selected_Component
            | N_Slice
            =>
            Set_Perm_Prefixes_Assign (+Prefix (N.Expr));

         when N_Qualified_Expression
            | N_Type_Conversion
            | N_Unchecked_Type_Conversion
            =>
            Set_Perm_Prefixes_Assign (+Expression (N.Expr));

         when others =>
            raise Program_Error;
         end case;
      end if;
   end Set_Perm_Prefixes_Assign;

   -------------------
   -- Setup_Globals --
   -------------------

   procedure Setup_Globals (Subp : Entity_Id) is
      Pragma_Node : Node_Id := Empty;
      --  Node containing the closest Global or Depends pragma in the scopes of
      --  Subp. It is used only for locating the error messages.
      Global_Ids  : Flow_Id_Sets.Set;
      --  Global variables referenced in this pragma

      procedure Setup_Global
        (Expr       : Expr_Or_Ent;
         Typ        : Entity_Id;
         Kind       : Formal_Kind;
         Subp       : Entity_Id;
         Global_Var : Boolean);
      --  Proxy procedure to set up globals, to adjust for the type of first
      --  parameter expected by Setup_Parameter_Or_Global.

      ------------------
      -- Setup_Global --
      ------------------

      procedure Setup_Global
        (Expr       : Expr_Or_Ent;
         Typ        : Entity_Id;
         Kind       : Formal_Kind;
         Subp       : Entity_Id;
         Global_Var : Boolean)
      is
         Expl : constant Node_Id :=
           (if Present (Pragma_Node)
            and then Global_Ids.Contains (Direct_Mapping_Id (Expr.Ent))
            then Pragma_Node
            else Expr.Ent);
         --  Node where Expr is declared with the current visibility. It can be
         --  a global or depends pragma of an enclosing unit or the declaration
         --  of the entity.

      begin
         Setup_Parameter_Or_Global
           (Id         => Expr.Ent,
            Typ        => Typ,
            Kind       => Kind,
            Subp       => Subp,
            Global_Var => Global_Var,
            Expl       => Expl);
      end Setup_Global;

      procedure Setup_Globals_Inst is new Handle_Globals (Setup_Global);

   --  Start of processing for Setup_Globals

      Scop : Entity_Id := Subp;

   begin
      --  Search for the first scope of Subp which has an explicit global or
      --  depends contract if any.

      loop
         if Is_Subprogram_Or_Entry (Scop) then
            Pragma_Node := Get_Pragma (Scop, Pragma_Global);
            if No (Pragma_Node) then
               Pragma_Node := Get_Pragma (Scop, Pragma_Depends);
            end if;
            exit when Present (Pragma_Node);
         end if;
         Scop := Scope (Scop);
         exit when No (Scop);
      end loop;

      --  If one has been found, store its global variables in Global_Ids

      if Present (Pragma_Node) then
         declare
            Write_Ids : Flow_Id_Sets.Set;

         begin
            Flow_Utility.Get_Proof_Globals (Subprogram      => Scop,
                                            Reads           => Global_Ids,
                                            Writes          => Write_Ids,
                                            Erase_Constants => False);

            Global_Ids.Union (Write_Ids);
         end;
      end if;

      Setup_Globals_Inst (Subp, Loc => Empty);
   end Setup_Globals;

   -------------------------------
   -- Setup_Parameter_Or_Global --
   -------------------------------

   procedure Setup_Parameter_Or_Global
     (Id         : Entity_Id;
      Typ        : Entity_Id;
      Kind       : Formal_Kind;
      Subp       : Entity_Id;
      Global_Var : Boolean;
      Expl       : Node_Id)
   is
      Perm : Perm_Kind_Option;

   begin
      case Kind is
         when E_In_Parameter =>

            --  Shallow parameters and globals need not be considered

            if not Is_Deep (Typ) then
               Perm := None;

            --  Use the permission of the declaration for global variables to
            --  have better error messages in the case of generated globals.
            --  The problematic case is a global variable which is moved by
            --  the subprogram, but is only read so flow analysis tags it as a
            --  global input. It seems clearer to complain at the end of the
            --  scope when the variable is not assigned back, than to emit a
            --  strange message stating that the variable was declared as
            --  read-only by a flow generated contract.

            elsif Global_Var then
               Perm := (if Is_Read_Only (Id) then Read_Only else Read_Write);

            --  Inputs of functions have R permission only

            elsif Ekind (Subp) = E_Function then
               Perm := Read_Only;

            --  Anonymous access to constant is an observe

            elsif Is_Anonymous_Access_Type (Typ)
              and then Is_Access_Constant (Typ)
            then
               Perm := Read_Only;

            --  Other access types are a borrow

            elsif Is_Access_Type (Typ) then
               Perm := Read_Write;

            --  Deep types other than access types define an observe

            else
               Perm := Read_Only;
            end if;

         when E_Out_Parameter
            | E_In_Out_Parameter
         =>
            --  Shallow parameters and globals need not be considered

            if not Is_Deep (Typ) then
               Perm := None;

            --  Functions cannot have outputs in SPARK

            elsif Ekind (Subp) = E_Function then
               return;

            --  Deep types define a borrow or a move

            else
               Perm := Read_Write;
            end if;
      end case;

      if Perm /= None then
         declare
            Tree : constant Perm_Tree_Access :=
              new Perm_Tree_Wrapper'
                (Tree =>
                   (Kind                => Entire_Object,
                    Is_Node_Deep        => Is_Deep (Etype (Id)),
                    Explanation         => Expl,
                    Permission          => Perm,
                    Children_Permission => Perm));
         begin
            Set (Current_Perm_Env, Id, Tree);
         end;
      end if;
   end Setup_Parameter_Or_Global;

   ----------------------
   -- Setup_Parameters --
   ----------------------

   procedure Setup_Parameters (Subp : Entity_Id) is
      Formal : Entity_Id;
   begin
      Formal := First_Formal (Subp);
      while Present (Formal) loop
         Setup_Parameter_Or_Global
           (Id         => Formal,
            Typ        => Retysp (Etype (Formal)),
            Kind       => Ekind (Formal),
            Subp       => Subp,
            Global_Var => False,
            Expl       => Formal);
         Next_Formal (Formal);
      end loop;
   end Setup_Parameters;

   --------------------------------
   -- Setup_Protected_Components --
   --------------------------------

   procedure Setup_Protected_Components (Subp : Entity_Id) is
      Typ  : constant Entity_Id := Scope (Subp);
      Comp : Entity_Id;
      Kind : Formal_Kind;

   begin
      Comp := First_Component_Or_Discriminant (Typ);

      --  The protected object is an implicit input of protected functions, and
      --  an implicit input-output of protected procedures and entries.

      if Ekind (Subp) = E_Function then
         Kind := E_In_Parameter;
      else
         Kind := E_In_Out_Parameter;
      end if;

      while Present (Comp) loop
         Setup_Parameter_Or_Global
           (Id         => Comp,
            Typ        => Retysp (Etype (Comp)),
            Kind       => Kind,
            Subp       => Subp,
            Global_Var => False,
            Expl       => Comp);

         Next_Component_Or_Discriminant (Comp);
      end loop;
   end Setup_Protected_Components;

end Gnat2Why.Borrow_Checker;
