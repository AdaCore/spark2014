------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--               G N A T 2 W H Y - B O R R O W _ C H E C K E R              --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2017-2025, AdaCore                     --
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

with Ada.Containers;            use Ada.Containers;
with Ada.Containers.Vectors;
with Ada.Unchecked_Deallocation;
with Atree;                     use Atree;
with Checked_Types;             use Checked_Types;
with Common_Containers;         use Common_Containers;
with Common_Iterators;          use Common_Iterators;
with Einfo.Entities;            use Einfo.Entities;
with Einfo.Utils;               use Einfo.Utils;
with Errout_Wrapper;            use Errout_Wrapper;
with Flow_Types;                use Flow_Types;
with Flow_Utility;              use Flow_Utility;
with GNAT.Dynamic_HTables;      use GNAT.Dynamic_HTables;
with Gnat2Why.Util;             use Gnat2Why.Util;
with Namet;                     use Namet;
with Nlists;                    use Nlists;
with Sem_Util;                  use Sem_Util;
with Sem_Aggr;                  use Sem_Aggr;
with Sem_Aux;                   use Sem_Aux;
with Sinfo.Nodes;               use Sinfo.Nodes;
with Sinfo.Utils;               use Sinfo.Utils;
with Snames;                    use Snames;
with SPARK_Definition;          use SPARK_Definition;
with SPARK_Definition.Annotate; use SPARK_Definition.Annotate;
with SPARK_Util;                use SPARK_Util;
with SPARK_Util.Subprograms;    use SPARK_Util.Subprograms;
with SPARK_Util.Types;          use SPARK_Util.Types;
with Treepr;                    use Treepr;
with VC_Kinds;                  use VC_Kinds;

use all type Ada.Containers.Count_Type;

package body Gnat2Why.Borrow_Checker is

   function Is_Read_Only (E : Entity_Id) return Boolean
   with Pre => Is_Object (E);
   --  Return True if E is declared as Read_Only (ie. a constant which is not
   --  of access-to-variable type, or a variable of anonymous
   --  access-to-constant type)

   function Unique_Entity_In_SPARK (E : Entity_Id) return Entity_Id
   is (if E in E_Constant_Id
         and then Present (Full_View (E))
         and then Entity_In_SPARK (Full_View (E))
       then Full_View (E)
       else E);
   --  Only go to the full view of constants if it is in SPARK

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

      package Perm_Tree_Maps is new
        Simple_HTable
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
               --  pointed to is given in Get_All. The permission of the
               --  Is_Null conceptual field is given in Null_Permission.

            when Reference =>
               Null_Permission : Perm_Kind;
               Get_All         : Perm_Tree_Access;

               --  Unfolded path of array type. The permission of elements is
               --  given in Get_Elem, permission of bounds is given in
               --  Bounds_Permission.

            when Array_Component =>
               Bounds_Permission : Perm_Kind;
               Get_Elem          : Perm_Tree_Access;

               --  Unfolded path of record type. The permission of the
               --  components is given in Component.

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

      function Query_Mutable_Tree_With_Default
        (T : in out Perm_Env; K : Entity_Id; Default_Env : Perm_Env)
         return Perm_Tree_Access;
      --  Wrapper around get. In case the key is not present, it tries putting
      --  a copy of the tree from Default_Env in T before querying again.
      --  The default environment is used to avoid cluterring the main
      --  permissions environments with typically useless and redundant data,
      --  which can get expensive on code with both many variables and paths.

      function Query_Read_Only_Tree_With_Default
        (T : Perm_Env; K : Entity_Id; Default_Env : Perm_Env)
         return Perm_Tree_Access;
      --  Wrapper around Get. In case the key is not present, it tries getting
      --  it from Default_Env. The functionality is similar to
      --  Query_Mutable_Tree_With_Default, except that due to the absence of
      --  copying, the resulting tree should not be mutated.

      type Perm_Env_Access is access Perm_Env;
      --  Access to permission environments

      package Env_Maps is new
        Simple_HTable
          (Header_Num => Elaboration_Context_Index,
           Key        => Node_Id,
           Element    => Perm_Env_Access,
           No_Element => null,
           Hash       => Elaboration_Context_Hash,
           Equal      => "=");
      --  The instantiation of a hash table whose elements are permission
      --  environments. This hash table is used to save the environments:
      --   * at the entry of each loop, with the key being the loop label,
      --   * at a goto label, with the key being the goto label entity, and
      --   * at exception handlers, with the keys being the node of the
      --     handler.

      type Env_Backups is new Env_Maps.Instance;
      --  The type defining the hash table saving the environments

      package Variable_Maps is new
        Simple_HTable
          (Header_Num => Elaboration_Context_Index,
           Key        => Entity_Id,
           Element    => Node_Vectors.Vector,
           No_Element => Node_Vectors.Empty_Vector,
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

      function Bounds_Permission (T : Perm_Tree_Access) return Perm_Kind;
      function Children_Permission (T : Perm_Tree_Access) return Perm_Kind;
      function Component (T : Perm_Tree_Access) return Perm_Tree_Maps.Instance;
      function Explanation (T : Perm_Tree_Access) return Node_Id;
      function Get_All (T : Perm_Tree_Access) return Perm_Tree_Access;
      function Get_Elem (T : Perm_Tree_Access) return Perm_Tree_Access;
      function Is_Node_Deep (T : Perm_Tree_Access) return Boolean;
      function Kind (T : Perm_Tree_Access) return Path_Kind;
      function Null_Permission (T : Perm_Tree_Access) return Perm_Kind;
      function Permission (T : Perm_Tree_Access) return Perm_Kind;

      -----------------------
      -- Memory Management --
      -----------------------

      procedure Copy_Env (From : Perm_Env; To : in out Perm_Env);
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

      procedure Reset_Env (PE : in out Perm_Env);
      --  Procedure to remove all restrictions from a permission environment.
      --  This is currently implemented by Free_Env since we can just default
      --  to Default_Perm_Env, but the intent of the two procedures is
      --  different. The implementation historically differed as well, since
      --  for Reset_Env we need the environment to behave as if all variables
      --  in the scope are still in it. For Free_Env we just want the
      --  allocated ressources gone, essentially invalidating the environment.
      --  We keep both routines in case the implementation diverges again.

      procedure Free_Tree (PT : in out Perm_Tree_Access);
      --  Procedure to free a permission tree

   end Permissions;

   package body Permissions is

      -----------------------
      -- Bounds_Permission --
      -----------------------

      function Bounds_Permission (T : Perm_Tree_Access) return Perm_Kind is
      begin
         return T.all.Tree.Bounds_Permission;
      end Bounds_Permission;

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
                  Comp_From  : Perm_Tree_Access;
                  Key_From   : Perm_Tree_Maps.Key_Option;
                  Son        : Perm_Tree_Access;
                  Hash_Table : Perm_Tree_Maps.Instance;
               begin
                  --  We put a new hash table, so that it gets dealiased from
                  --  the Component (From) hash table.
                  To.all.Tree.Component := Hash_Table;
                  Key_From := Perm_Tree_Maps.Get_First_Key (Component (From));

                  while Key_From.Present loop
                     Comp_From :=
                       Perm_Tree_Maps.Get (Component (From), Key_From.K);
                     pragma Assert (Comp_From /= null);
                     Son := new Perm_Tree_Wrapper;
                     Copy_Tree (Comp_From, Son);
                     Perm_Tree_Maps.Set
                       (To.all.Tree.Component, Key_From.K, Son);
                     Key_From :=
                       Perm_Tree_Maps.Get_Next_Key (Component (From));
                  end loop;
               end;
         end case;
      end Copy_Tree;

      ------------------------------
      -- Elaboration_Context_Hash --
      ------------------------------

      function Elaboration_Context_Hash
        (Key : Entity_Id) return Elaboration_Context_Index is
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
      -- Reset_Env --
      ---------------

      procedure Reset_Env (PE : in out Perm_Env) renames Free_Env;

      ---------------
      -- Free_Tree --
      ---------------

      procedure Free_Tree (PT : in out Perm_Tree_Access) is
         procedure Free_Perm_Tree_Dealloc is new
           Ada.Unchecked_Deallocation (Perm_Tree_Wrapper, Perm_Tree_Access);
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
         To := From;
         From := Perm_Env (Perm_Tree_Maps.Nil);
      end Move_Env;

      ---------------------------
      -- Move_Variable_Mapping --
      ---------------------------

      procedure Move_Variable_Mapping (From, To : in out Variable_Mapping) is
      begin
         Reset (To);
         To := From;
         From := Variable_Mapping (Variable_Maps.Nil);
      end Move_Variable_Mapping;

      ---------------------
      -- Null_Permission --
      ---------------------

      function Null_Permission (T : Perm_Tree_Access) return Perm_Kind is
      begin
         return T.all.Tree.Null_Permission;
      end Null_Permission;

      ----------------
      -- Permission --
      ----------------

      function Permission (T : Perm_Tree_Access) return Perm_Kind is
      begin
         return T.all.Tree.Permission;
      end Permission;

      -------------------------------------
      -- Query_Mutable_Tree_With_Default --
      -------------------------------------

      function Query_Mutable_Tree_With_Default
        (T : in out Perm_Env; K : Entity_Id; Default_Env : Perm_Env)
         return Perm_Tree_Access is
      begin
         return Res : Perm_Tree_Access := Get (T, K) do
            if Res = null then
               declare
                  Temp : Perm_Tree_Access := Get (Default_Env, K);
               begin
                  if Temp /= null then
                     Res := new Perm_Tree_Wrapper;
                     Copy_Tree (From => Temp, To => Res);
                     Set (T, K, Res);
                  end if;
               end;
            end if;
         end return;
      end Query_Mutable_Tree_With_Default;

      ---------------------------------------
      -- Query_Read_Only_Tree_With_Default --
      ---------------------------------------

      function Query_Read_Only_Tree_With_Default
        (T : Perm_Env; K : Entity_Id; Default_Env : Perm_Env)
         return Perm_Tree_Access is
      begin
         return Res : Perm_Tree_Access := Get (T, K) do
            if Res = null then
               Res := Get (Default_Env, K);
            end if;
         end return;
      end Query_Read_Only_Tree_With_Default;

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

      Free,
      --  Used for the actual parameter of a call to an instance of
      --  Unchecked_Deallocation. If the designated type of the pointer given
      --  in argument is deep, it checks that the path corresponding to the
      --  pointed-to object has Write_Perm permission, as this allows moving
      --  the pointed-to objects but not moving the argument pointer (otherwise
      --  the pointed-to object would have No_Access permission). Otherwise
      --  (the designated type is not deep), it checks that the path
      --  corresponding to the argument has permission Read_Write (same as
      --  for Move).

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
         when Folded =>
            Found_Permission : Perm_Kind;
            Explanation      : Node_Id;

         when Unfolded =>
            Tree_Access : Perm_Tree_Access;
      end case;
   end record;

   type Expr_Or_Ent (Is_Ent : Boolean) is record
      case Is_Ent is
         when False =>
            Expr : Node_Id;

         when True =>
            Ent : Entity_Id;
            Loc : Node_Id;
      end case;
   end record;

   -----------------------
   -- Local subprograms --
   -----------------------

   function "+" (X : Node_Id) return Expr_Or_Ent
   is ((Is_Ent => False, Expr => X));

   function "<" (P1, P2 : Perm_Kind) return Boolean;
   function Glb (P1, P2 : Perm_Kind) return Perm_Kind;
   function Lub (P1, P2 : Perm_Kind) return Perm_Kind;

   procedure Setup_Environment_For_Object
     (Name : Entity_Id; Perm : Perm_Kind; Expl : Node_Id)
   with Pre => Perm in Read_Only | Read_Write;
   --  Extends current permission environment with declaration of variable
   --  Name, with initial permission Perm.

   procedure Check_Assignment (Target : Node_Or_Entity_Id; Expr : Node_Id);
   --  Handle assignment as part of an assignment statement or an object
   --  declaration.

   procedure Check_Call_With_Side_Effects (Call : Node_Id);

   procedure Check_Callable_Body (Id : Entity_Id);
   --  Entry point for the analysis of a subprogram or entry body

   procedure Check_Declaration (Decl : Node_Id);

   procedure Check_End_Of_Scope (Decls : List_Id; N : Node_Id := Empty);
   --  Check that local borrowers are in the Unrestricted state before
   --  releasing ownership back to the borrowed object. If present, N is the
   --  node used for error location, otherwise the error is reported on the
   --  borrower's declaration.

   procedure Check_Transfer_Of_Control
     (From : Node_Id; Unconditional : Boolean := False);
   --  For From a transfer-of-control statements:
   --  * Check the sequence of finally statements from From to any
   --    reachable destination, accumulating the final environment in the
   --    destination accumulator (Current_Loops_Accumulators,
   --    Current_Goto_Accumulators, or Current_Exc_Accumulators)
   --  * For exited scopes, check that local borrowers are in the unrestricted
   --    state before releasing ownership back to the borrowed object.
   --  If the subprogram is exited, permissions on globals/output parameters
   --  are checked to be unrestricted as well.
   --
   --  If Unconditional is set to True, the transfer of control is considered
   --  to always happen, and Current_Perm_Env is emptied as the path is cut.

   procedure Check_Expression (Expr : Node_Id; Mode : Extended_Checking_Mode)
   with
     Pre =>
       Nkind (Expr)
       in N_Index_Or_Discriminant_Constraint
        | N_Range_Constraint
        | N_Subtype_Indication
        | N_Digits_Constraint
        | N_Delta_Constraint
        | N_Subexpr;

   procedure Check_Expr_Or_Ent
     (Expr : Expr_Or_Ent; Mode : Extended_Checking_Mode)
   with
     Pre =>
       (Expr.Is_Ent
        or else Nkind (Expr.Expr)
                in N_Index_Or_Discriminant_Constraint
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

   function Check_On_Borrowed (Expr : Expr_Or_Ent) return Node_Id;
   --  Return a previously borrowed expression in conflict with Expr if any

   function Check_On_Observed (Expr : Expr_Or_Ent) return Node_Id;
   --  Return a previously observed expression in conflict with Expr if any

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
      Param      : Entity_Id;
      Typ        : Entity_Id;
      Kind       : Formal_Kind;
      Subp       : Entity_Id;
      Global_Var : Boolean);
   --  Check the permission of every actual parameter or global

   procedure Check_Pragma (Prag : Node_Id);

   procedure Check_Simple_Return_Expression
     (Expr : N_Subexpr_Id; Subp : Entity_Id);
   --  Check a simple return statement with an expression Expr

   procedure Check_Statement (Stmt : Node_Id);

   type Perm_And_Expl is record
      Perm : Perm_Kind;
      Expl : Node_Id;
   end record;
   function Get_Perm_And_Expl
     (N : Expr_Or_Ent; Under_Dereference : Boolean := False)
      return Perm_And_Expl;
   --  The function that takes a name as input and returns a permission
   --  associated with it, together with an explanation node.
   --  If Under_Dereference is True, it return the greatest lower bound (meet)
   --  of permissions for parts potentially accessible under dereference (.all)
   --  from N, together with a matching explanation node.

   function Get_Perm_Or_Tree (N : Expr_Or_Ent) return Perm_Or_Tree;
   pragma Precondition (N.Is_Ent or else Is_Path_Expression (N.Expr));
   --  This function gets a node and looks recursively to find the appropriate
   --  subtree for that node. If the tree is folded on that node, then it
   --  returns the permission given at the right level.
   --  If a tree is returned, it must be used in read-only fashion.

   function Get_Perm_Tree (N : Expr_Or_Ent) return Perm_Tree_Access;
   pragma Precondition (N.Is_Ent or else Is_Path_Expression (N.Expr));
   --  This function gets a node and looks recursively to find the appropriate
   --  subtree for that node. If the tree is folded, then it unrolls the tree
   --  up to the appropriate level.

   generic
      with
        procedure Handle_Parameter_Or_Global
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

   function Is_Move_To_Constant (Expr : Node_Id) return Boolean
   with Pre => Is_Access_Constant (Retysp (Etype (Expr)));
   --  Even if the type of Expr is not deep, an assignment can still be a
   --  move. It occurs on allocators and conversions to access-to-constant
   --  types.

   function Is_Prefix_Or_Almost
     (Pref : Node_Id; Expr : Expr_Or_Ent) return Boolean;
   --  Determine if the candidate Prefix is indeed a prefix of Expr, or almost
   --  a prefix, in the sense that they could still refer to overlapping memory
   --  locations.

   procedure Merge_Env
     (Source : in out Perm_Env;
      Target : in out Perm_Env;
      Filter : Boolean := False);
   --  Merge Target and Source into Target, and then deallocate the Source
   --  If Filter is True, first filter source by the variables declared in
   --  scopes, as tracked by Default_Perm_Env.
   --
   --  A value of False remains relevant for accumulating environments at
   --  join points (at the end of a conditional branch, or at statements that
   --  transfer control). At such points, we are accumulating Current_Perm_env,
   --  which is kept filtered, so additional filtering would be useless.
   --  A more useful filter in these cases would be the objects declared in the
   --  scope of the transfer-of-control target, to avoid accumulating values we
   --  will filter later on, but keeping track of such information would be
   --  more complex.

   procedure Merge_Transfer_Of_Control_Env
     (Map : in out Env_Backups; Key : Node_Id);
   --  Used at transfer-of-control target points, to merge environments stored
   --  for the target in the current environment. Map, Key must be the
   --  corresponding maps/key corresponding to the target. After merge, the key
   --  is removed from the map.

   procedure BC_Error
     (Msg           : Message;
      N             : Node_Id;
      Continuations : Message_Lists.List := Message_Lists.Empty);
   --  Common mechanism to emit errors in the borrow checker. Call Error_Msg_N
   --  and set Permission_Error.

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

   procedure Perm_Error_Borrow_End
     (E : Entity_Id; N : Node_Id; Found_Perm : Perm_Kind; Expl : Node_Id);
   --  A procedure that is called when the permissions found contradict the
   --  rules established by the RM at the end of a borrow. This function is
   --  called with the borrower, the node for error location, and adds an
   --  error message with the appropriate values.

   procedure Perm_Error_Subprogram_End
     (E           : Entity_Id;
      Subp        : Entity_Id;
      Found_Perm  : Perm_Kind;
      Expl        : Node_Id;
      Exceptional : Boolean);
   --  A procedure that is called when the permissions found contradict the
   --  rules established by the RM at the end of subprograms. This function is
   --  called with the node, the node of the returning function, and adds an
   --  error message with the appropriate values.

   procedure Perm_Error_Reborrow
     (E : Entity_Id; N : Node_Id; Found_Perm : Perm_Kind; Expl : Node_Id);
   --  A procedure that is called when the permissions found contradict the
   --  rules established by the RM at a reborrow. This function is called with
   --  the borrower, the node for error location, and adds an error message
   --  with the appropriate values.

   function Perm_Mismatch
     (N              : Expr_Or_Ent;
      Exp_Perm       : Perm_Kind;
      Act_Perm       : Perm_Kind;
      Expl           : Node_Id;
      Forbidden_Perm : Boolean := False) return Message;
   --  Return a continuation error message about a mismatch between a desired
   --  permission Exp_Perm and a permission obtained Act_Perm. N is the root
   --  of the path leading to the error.

   procedure Process_Path (Expr : Expr_Or_Ent; Mode : Checking_Mode);
   pragma Precondition (Expr.Is_Ent or else Is_Path_Expression (Expr.Expr));
   --  Check correct permission for the path in the checking mode Mode, and
   --  update permissions of the path and its prefixes/extensions.

   procedure Return_Globals (Subp : Entity_Id; Exceptional : Boolean := False);
   --  Takes a subprogram as input, and checks that all borrowed global items
   --  of the subprogram indeed have Read_Write permission at the end of the
   --  subprogram execution.

   procedure Return_Parameter_Or_Global
     (Id : Entity_Id; Subp : Entity_Id; Exceptional : Boolean);
   --  Auxiliary procedure to Return_Parameters and Return_Globals

   procedure Return_Parameters
     (Subp : Entity_Id; Exceptional : Boolean := False);
   --  Takes a subprogram as input, and checks that all out parameters of the
   --  subprogram indeed have Read_Write permission at the end of the
   --  subprogram execution.

   procedure Return_Protected_Components (Subp : Entity_Id);
   --  Takes a protecture procedure or entry as input, and checks that all
   --  protected components of the corresponding implicit parameter indeed
   --  have Read_Write permission at the end of the subprogram execution.

   procedure Set_Perm_Extensions
     (T : Perm_Tree_Access; P : Perm_Kind; Expl : Node_Id);
   --  This procedure takes an access to a permission tree and modifies the
   --  tree so that any strict extensions of the given tree become of the
   --  access specified by parameter P.

   procedure Set_Perm_Extensions_Move
     (T : Perm_Tree_Access; E : Entity_Id; Expl : Node_Id);
   --  Set permissions to
   --    No for any extension with more .all
   --    W for any deep extension with same number of .all
   --    RW for any shallow extension with same number of .all

   function Set_Perm_Prefixes
     (N           : Expr_Or_Ent;
      Perm        : Perm_Kind_Option;
      Expl        : Node_Id;
      Move_Access : Boolean := False) return Perm_Tree_Access;
   pragma Precondition (N.Is_Ent or else Is_Path_Expression (N.Expr));
   pragma Precondition (if Move_Access then Perm = No_Access);
   --  This function modifies the permissions of a given node in the permission
   --  environment as well as all the prefixes of the path, to the new
   --  permission Perm. The general rule here is that everybody updates the
   --  permission of the subtree they are returning.
   --  If Move_Access is True, the prefixes of the path are set to the
   --  permission No_Access until a dereference is found, and Write_Only
   --  afterward.

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

   Default_Perm_Env : Perm_Env;
   --  Permission environment storing initial permissions for variables.
   --  This is used:
   --  * To guarantee consistency of permission decisions between environment
   --    setup, reset, and expected permission at end-of-subprogram. This
   --    effectively centralize the computation of the expected initial
   --    permission.
   --  * For performance reasons, to avoid put shallow variables in the
   --    permission environments. In > 95% of the case, there are not
   --    involved in borrow-checking at all. When they are truly needed,
   --    we make a copy.

   function Query_Mutable_Tree
     (T           : in out Perm_Env;
      K           : Entity_Id;
      Default_Env : Perm_Env := Default_Perm_Env) return Perm_Tree_Access
   is (Query_Mutable_Tree_With_Default (T, K, Default_Env));
   --  Wrapper over Query_Mutable_Tree_With_Default, which sets default to
   --  Default_Perm_Env. All queries to permission environments should be done
   --  through Query_*_Tree, except for specific performance optimizations.

   function Query_Read_Only_Tree
     (T : Perm_Env; K : Entity_Id; Default_Env : Perm_Env := Default_Perm_Env)
      return Perm_Tree_Access
   is (Query_Read_Only_Tree_With_Default (T, K, Default_Env));
   --  Matching wrapper for Query_Read_Only_With_Default

   Inside_Procedure_Call : Boolean := False;
   --  Set while checking the actual parameters of a procedure or entry call

   Inside_Elaboration : Boolean := False;
   --  Set during package spec/body elaboration, during which move and local
   --  observe/borrow are not allowed. As a result, no other checking is needed
   --  during elaboration.

   For_Program_Exit : Boolean := False;
   --  Set during the checks for globals mentioned in the Program_Exit contract
   --  of the current subprogram on calls to subprograms which might exit the
   --  program. It is used to add a continuation to the generated checks.

   Current_Subp : Entity_Id := Empty;
   --  Set to the enclosing unit during the analysis of a callable body

   Current_Exit_Accumulators : Env_Backups;
   --  This variable contains the environments used as accumulators for loops,
   --  that consist of the merge of all environments at each exit point of
   --  the loop (which can also be the entry point of the loop in the case of
   --  non-infinite loops), each of them reachable from the label of the loop.
   --  We require that the environment stored in the accumulator be less
   --  restrictive than the saved environment at the beginning of the loop, and
   --  the permission environment after the loop is equal to the accumulator.

   Current_Continue_Accumulators : Env_Backups;
   --  This variable contains the environments used as accumulators for loop
   --  continues, that consists of the merge of all environments at each
   --  continue statements mentioning the given loop. When the completion of
   --  the loop is encountered, this environment is merged with the current
   --  one.

   Current_Goto_Accumulators : Env_Backups;
   --  This variable contains the environments used as accumulators for goto
   --  labels, that consist of the merge of all environments at each goto
   --  statements mentioning this label. When a goto label is encountered, this
   --  environment is merged with the current one.

   Current_Exc_Accumulators : Env_Backups;
   --  This variable contains the environments used as accumulators for
   --  exception handling, that consist of the merge of all environments at
   --  each raise or call statements which might jump to the handler. When such
   --  a statement is encountered, this environment is merged with the current
   --  one.

   Current_Extended_Return_Accumulators : Env_Backups;
   --  This variable contains the environments used as accumulators for
   --  completion of extended returns, which are targeted by inner
   --  return statements.

   Current_Borrowers : Variable_Mapping;
   --  Mapping from borrowers to the paths borrowed (only one for borrowers)

   Current_Observers : Variable_Mapping;
   --  Mapping from observers to the paths observed

   Permission_Error : Boolean := False;
   --  Should be set to true when an error message is emitted

   ----------------------
   -- Scope management --
   ----------------------

   package Object_Scope is

      --  The following procedure track the objects declared in the current
      --  scope. They are tracked in an implicit stack, divided in consecutive
      --  sectors. These sectors can be empty. The initial value of the
      --  implicit stack is empty, with a single empty sector.

      procedure Push_Object (E : Entity_Id);
      --  Push a new object on the implicit stack, within the last sector. This
      --  should be called when processing a declaration of a construct, before
      --  processing the sub-construct that see the declaration.

      procedure Push_Scope;
      --  Add a new empty sector at the end of the object stack

      procedure Pop_Scope;
      --  Remove the last sector at the end of the object stack. The
      --  corresponding object entities are also removed from Default/Current
      --  permission environments.
      --
      --  In essence, if there is a call to Push_Scope when we start processing
      --  a construct, there should be a call to Pop_Scope at the end.
      --
      --  Pop_Scope can only be called if there are at least 2 sectors in the
      --  implicit stack. That is, the initial sector cannot be popped, only
      --  sectors introduced by Push_Scope can.

      function Is_Initial_Value return Boolean
      with Ghost;
      --  For sanity checking: return whether the implicit stack is at its
      --  initial value.

   end Object_Scope;

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
           (Expr       => Expr_Or_Ent'(Is_Ent => True, Ent => E, Loc => Loc),
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

   ---------
   -- "<" --
   ---------

   function "<" (P1, P2 : Perm_Kind) return Boolean is

      function ">=" (P1, P2 : Perm_Kind) return Boolean;
      --  Return if permission P1 is more restrictive than P2

      function ">=" (P1, P2 : Perm_Kind) return Boolean is
      begin
         case P2 is
            when No_Access =>
               return True;

            when Read_Only =>
               --  When a loop starts with permission Read_Only for an object,
               --  this permission cannot change by the end of the loop, so
               --  P1 = P2 and function "<" does not even call ">=".
               pragma
                 Annotate
                   (Xcov,
                    Exempt_On,
                    "Impossible case with P1"
                      & " and P2 permissions around a loop");
               return P1 in Read_Perm;
               pragma Annotate (Xcov, Exempt_Off);

            when Write_Only =>
               return P1 in Write_Perm;

            when Read_Write =>
               return P1 = Read_Write;
         end case;
      end ">=";

   begin
      return P1 /= P2 and then P2 >= P1;
   end "<";

   --------------------------------
   -- Set_Environment_For_Object --
   --------------------------------

   procedure Setup_Environment_For_Object
     (Name : Entity_Id; Perm : Perm_Kind; Expl : Node_Id)
   is
      Name_Is_Deep : constant Boolean := Is_Deep (Etype (Name));
      Tree         : Perm_Tree_Access;
      Old_Tree     : constant Perm_Tree_Access :=
        Query_Read_Only_Tree (Current_Perm_Env, Name);
   begin
      --  During setup of package elaboration globals, entities can be
      --  referenced multiple times. This can also happen because we go through
      --  expression twice, but do not clean up (variable in declare
      --  expressions for example). The addition should always be consistent
      --  with the environment in that case.

      if Old_Tree /= null then
         if Kind (Old_Tree) = Entire_Object
           and then Permission (Old_Tree) = Perm
           and then Children_Permission (Old_Tree) = Perm
           and then Is_Node_Deep (Old_Tree) = Name_Is_Deep
         then
            return;
         else
            raise Program_Error;
         end if;
      end if;

      Tree :=
        new Perm_Tree_Wrapper'
          (Tree =>
             (Kind                => Entire_Object,
              Is_Node_Deep        => Name_Is_Deep,
              Explanation         => Expl,
              Permission          => Perm,
              Children_Permission => Perm));

      Set (Default_Perm_Env, Name, Tree);
      Object_Scope.Push_Object (Name);

   end Setup_Environment_For_Object;

   --------------
   -- BC_Error --
   --------------

   procedure BC_Error
     (Msg           : Message;
      N             : Node_Id;
      Continuations : Message_Lists.List := Message_Lists.Empty)
   is
      Conts : Message_Lists.List := Continuations;
   begin
      if For_Program_Exit then
         Conts.Append (Create ("when exiting the program"));
      end if;
      Error_Msg_N (Msg, N, Continuations => Conts);
      Permission_Error := True;
   end BC_Error;

   ----------------------
   -- Check_Assignment --
   ----------------------

   procedure Check_Assignment (Target : Node_Or_Entity_Id; Expr : Node_Id) is
      Is_Decl : constant Boolean := Nkind (Target) = N_Defining_Identifier;

      --  Local subprograms

      procedure Check_Assignment_To_Ghost
        (Target_Root : Entity_Id; Expr_Root : Entity_Id; Mode : Checking_Mode);
      --  Check that move or borrow of Expr_Root into Target_Root does not
      --  violate the rule wrt ghost having no effect on non-ghost.

      procedure Handle_Borrow_Or_Observe
        (Map : in out Variable_Mapping; Var : Entity_Id; Expr : Node_Id);
      --  Update Map with a new borrow or observe Var := Expr

      procedure Handle_Borrow (Var : Entity_Id; Expr : Node_Id);
      --  Update map of current borrowers

      procedure Handle_Observe (Var : Entity_Id; Expr : Node_Id);
      --  Update map of current observers

      -------------------------------
      -- Check_Assignment_To_Ghost --
      -------------------------------

      --  SPARK RM 3.10(17): A path rooted at a non-ghost object shall only
      --  be moved, or borrowed, if the target object of the move or borrow
      --  is itself non-ghost and if the target object of a move or borrow is a
      --  disabled ghost object, then the moved or borrowed path shall be
      --  rooted at a disabled ghost object.

      procedure Check_Assignment_To_Ghost
        (Target_Root : Entity_Id; Expr_Root : Entity_Id; Mode : Checking_Mode)
      is
      begin
         if not Is_Ghost_Entity (Target_Root) or else No (Expr_Root) then
            null;

         elsif not Is_Ghost_Entity (Expr_Root) then
            BC_Error
              (Create
                 ("non-ghost object & cannot be "
                  & (case Mode is
                       when Borrow => "borrowed",
                       when Move => "moved",
                       when others => raise Program_Error)
                  & " in an assignment to ghost object &",
                  Names => [Expr_Root, Target_Root]),
               Expr);

         elsif not Is_Checked_Ghost_Entity (Target_Root)
           and then Is_Checked_Ghost_Entity (Expr_Root)
         then
            BC_Error
              (Create
                 ("enabled ghost object & cannot be "
                  & (case Mode is
                       when Borrow => "borrowed",
                       when Move => "moved",
                       when others => raise Program_Error)
                  & " in an assignment to disabled ghost object &",
                  Names => [Expr_Root, Target_Root]),
               Expr);

         elsif not Is_Same_Or_Depends_On_Level
                     (Ghost_Assertion_Level (Target_Root),
                      Ghost_Assertion_Level (Expr_Root))
           or else not Is_Same_Or_Depends_On_Level
                         (Ghost_Assertion_Level (Expr_Root),
                          Ghost_Assertion_Level (Target_Root))
         then
            BC_Error
              (Create
                 ("ghost object & cannot be "
                  & (case Mode is
                       when Borrow => "borrowed",
                       when Move => "moved",
                       when others => raise Program_Error)
                  & " in an assignment to ghost object &",
                  Names => [Expr_Root, Target_Root]),
               Expr,
               Continuations =>
                 [Create
                    ("& and & should have matching assertion levels",
                     Names => [Expr_Root, Target_Root])]);
         end if;
      end Check_Assignment_To_Ghost;

      -------------------
      -- Handle_Borrow --
      -------------------

      procedure Handle_Borrow (Var : Entity_Id; Expr : Node_Id) is
      begin
         Handle_Borrow_Or_Observe (Current_Borrowers, Var, Expr);
      end Handle_Borrow;

      ------------------------------
      -- Handle_Borrow_Or_Observe --
      ------------------------------

      procedure Handle_Borrow_Or_Observe
        (Map : in out Variable_Mapping; Var : Entity_Id; Expr : Node_Id)
      is
         Borrowed     : Node_Id;
         Borrowed_Bag : Node_Vectors.Vector;

      begin
         --  Insert in Map if we are in a declaration

         if Is_Decl then
            for Dep_Path of Terminal_Alternatives (Expr) loop
               Borrowed := Get_Observed_Or_Borrowed_Expr (Dep_Path);

               --  Path'Access borrows/observes Path

               if Nkind (Borrowed) = N_Attribute_Reference
                 and then Attribute_Name (Borrowed) = Name_Access
               then
                  Borrowed := Prefix (Borrowed);
               end if;
               Borrowed_Bag.Append (Borrowed);
            end loop;
            Set (Map, Var, Borrowed_Bag);
         else
            pragma Assert (Get_Root_Object (Expr) = Var);
         end if;
      end Handle_Borrow_Or_Observe;

      --------------------
      -- Handle_Observe --
      --------------------

      procedure Handle_Observe (Var : Entity_Id; Expr : Node_Id) is
      begin
         Handle_Borrow_Or_Observe (Current_Observers, Var, Expr);
      end Handle_Observe;

      --  Local variables

      Target_Typ  : constant Entity_Id := Etype (Target);
      Target_Root : Entity_Id;
      Expr_Root   : Entity_Id;
      Dummy       : Boolean := True;

      --  Start of processing for Check_Assignment

   begin
      --  For function calls with side effects, use the handling of
      --  procedure calls as there might be parameters of mode OUT.
      --  Such calls can never be borrows/observes as traversal
      --  functions cannot have side effects. No need to check the
      --  assignment for ghost compatibility as the returned object
      --  is necessarily new.

      if Nkind (Expr) = N_Function_Call
        and then Is_Function_With_Side_Effects (Get_Called_Entity (Expr))
      then
         Check_Call_With_Side_Effects (Call => Expr);

      elsif Is_Anonymous_Access_Object_Type (Target_Typ) then
         Expr_Root := Get_Root_Object (Expr);

         if Is_Decl then
            Target_Root := Target;

            --  Check that the root of the initial expression does not have
            --  overlays.

            if not Overlay_Alias (Expr_Root).Is_Empty
              and then not Is_Constant_In_SPARK (Expr_Root)
            then
               declare
                  Operation : constant String :=
                    (if Is_Access_Constant (Target_Typ)
                       or else Is_Constant_Borrower (Target_Root)
                     then "observed"
                     else "borrowed");
               begin
                  BC_Error
                    (Create
                       (Operation
                        & " object aliased through address clauses"
                        & " is not supported yet"),
                     Target);
               end;
            end if;
         else
            Target_Root := Get_Root_Object (Target);
         end if;

         --  SPARK RM 3.10(8): For an assignment statement where the target is
         --  a stand-alone object of an anonymous access-to-object type.

         pragma Assert (Present (Target_Root));

         --  If the destination root is a prophecy save, then marking
         --  forces the assignment to be the initialization of a
         --  constant declaration with highly specific shape.
         --  We only need to check that the initialization expression
         --  can be read, as it does not create any alias from the point of
         --  view of the borrow checker.

         if Is_Prophecy_Save (Target_Root) then
            pragma Assert (Is_Decl);
            Check_Expression (Expr, Read);

         --  If the type of the target is an anonymous access-to-constant type
         --  (an observing access type), the source shall be an owning access
         --  object denoted by a name that is not in the Moved state, and whose
         --  root object is not in the Moved state and is not declared at a
         --  statically deeper accessibility level than that of the target
         --  object.
         --  A borrower directly or indirectly borrowing the first parameter of
         --  a borrowing traversal function is also considered to be an
         --  observe.

         elsif Is_Access_Constant (Target_Typ)
           or else Is_Constant_Borrower (Target_Root)
         then
            --  The fact that a re-observe is always rooted at the observer for
            --  access to variable observe is checked in marking.

            pragma
              Assert
                (if not Is_Decl and then not Is_Access_Constant (Target_Typ)
                   then
                     Is_Entity_Name (Target) and then Target_Root = Expr_Root);

            Check_Expression (Expr, Observe);
            Handle_Observe (Target_Root, Expr);

         --  If the type of the target is an anonymous access-to-variable
         --  type (an owning access type), the source shall be an owning
         --  access object denoted by a name that is in the Unrestricted
         --  state, and whose root object is the target object itself.

         else
            --  The fact that a re-borrow is always rooted at the borrower is
            --  checked in marking.

            pragma
              Assert
                (if not Is_Decl
                   then
                     Is_Entity_Name (Target) and then Target_Root = Expr_Root);

            Check_Expression (Expr, Borrow);
            Check_Assignment_To_Ghost (Target_Root, Expr_Root, Borrow);
            Handle_Borrow (Target_Root, Expr);
         end if;

      elsif Is_Deep (Target_Typ) then
         Expr_Root := Get_Root_Object (Expr);

         if Is_Decl then
            Target_Root := Target;
         else
            Target_Root := Get_Root_Object (Target);
         end if;

         --  Expression not allowed as source of move

         pragma Assert (Is_Path_Expression (Expr));
         Check_Expression (Expr, Move);
         Check_Assignment_To_Ghost (Target_Root, Expr_Root, Move);

      elsif Is_Access_Type (Retysp (Target_Typ))
        and then Is_Access_Constant (Retysp (Target_Typ))
        and then Is_Move_To_Constant (Expr)
      then

         --  The expression of the conversion/allocator is moved. No checking
         --  is required wrt ghost as no write/deallocation is possible through
         --  the target object.

         pragma Assert (Is_Path_Expression (Expression (Expr)));
         Check_Expression (Expression (Expr), Move);

      else
         Check_Expression (Expr, Read);
      end if;
   end Check_Assignment;

   ----------------------------------
   -- Check_Call_With_Side_Effects --
   ----------------------------------

   procedure Check_Call_With_Side_Effects (Call : Node_Id) is

      Subp : constant Entity_Id := Get_Called_Entity (Call);

      --  Local subprograms

      procedure Check_Param (Formal : Entity_Id; Actual : Node_Id);
      --  Check the permission of every actual parameter

      procedure Check_Protected_Components (Subp : Entity_Id);
      --  Check the permission of the implicit parameter of an internal call to
      --  a protected procedure or entry.

      procedure Update_Param (Formal : Entity_Id; Actual : Node_Id);
      --  Update the permission of OUT actual parameters

      -----------------
      -- Check_Param --
      -----------------

      procedure Check_Param (Formal : Entity_Id; Actual : Node_Id) is
      begin
         Check_Parameter_Or_Global
           (Expr       => +Actual,
            Param      => Formal,
            Typ        => Etype (Formal),
            Kind       => Ekind (Formal),
            Subp       => Subp,
            Global_Var => False);
      end Check_Param;

      --------------------------------
      -- Check_Protected_Components --
      --------------------------------

      procedure Check_Protected_Components (Subp : Entity_Id) is

         procedure Check_Component (Comp : Entity_Id; Kind : Formal_Kind);
         --  Apply check to component of protected object

         ---------------------
         -- Check_Component --
         ---------------------

         procedure Check_Component (Comp : Entity_Id; Kind : Formal_Kind) is
         begin
            Check_Parameter_Or_Global
              (Expr       => (Is_Ent => True, Ent => Comp, Loc => Call),
               Param      => Comp,
               Typ        => Etype (Comp),
               Kind       => Kind,
               Subp       => Subp,
               Global_Var => False);
         end Check_Component;

         --  Local variables

         Typ  : constant Entity_Id := Scope (Subp);
         Kind : constant Formal_Kind :=
           (if Ekind (Subp) in E_Procedure | E_Entry
            then E_In_Out_Parameter
            else E_In_Parameter);
         --  The protected object is an implicit input-output of protected
         --  procedures and entries and an implicit input of functions (even
         --  functions with side effects).

      begin
         declare
            Comp : Entity_Id := First_Component_Or_Discriminant (Typ);
         begin
            while Present (Comp) loop
               Check_Component (Comp, Kind);
               Next_Component_Or_Discriminant (Comp);
            end loop;
         end;

         declare
            Anon_Obj : constant Entity_Id := Anonymous_Object (Scope (Subp));
         begin
            if Present (Anon_Obj) then
               for Comp of Iter (Part_Of_Constituents (Anon_Obj)) loop
                  Check_Component (Comp, Kind);
               end loop;
            end if;
         end;
      end Check_Protected_Components;

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

      procedure Check_Params is new Iterate_Call_Parameters (Check_Param);

      procedure Update_Params is new Iterate_Call_Parameters (Update_Param);

      --  Start of processing for Check_Call_With_Side_Effects

   begin
      Inside_Procedure_Call := True;
      Check_Params (Call);
      Check_Globals (Get_Called_Entity (Call), Call);

      --  For operations directly inside protected objects, check the
      --  permission of protected components on internal calls.

      if Ekind (Scope (Subp)) = E_Protected_Type
        and then not Is_External_Call (Call)
      then
         Check_Protected_Components (Subp);
      end if;

      Inside_Procedure_Call := False;
      Update_Params (Call);

      --  If Call might exit the program, make sure that all globals occuring
      --  in the Post_Exit of the enclosing subprogram can be read.

      if Might_Exit_Program (Call) then
         pragma
           Assert
             (Present (Current_Subp) and then Has_Program_Exit (Current_Subp));
         for G of Get_Outputs_From_Program_Exit (Current_Subp, Current_Subp)
         loop
            if G.Kind = Direct_Mapping then
               For_Program_Exit := True;
               Process_Path
                 ((Is_Ent => True, Ent => G.Node, Loc => Call), Read);
               For_Program_Exit := False;
            end if;
         end loop;
      end if;

      --  If Call might raise some exceptions, handle the exceptional paths

      if Might_Raise_Handled_Exceptions (Call) then
         Check_Transfer_Of_Control
           (Call,
            Unconditional =>
              Nkind (Call) = N_Procedure_Call_Statement
              and then No_Return (Get_Called_Entity (Call)));
      end if;
   end Check_Call_With_Side_Effects;

   -------------------------
   -- Check_Callable_Body --
   -------------------------

   procedure Check_Callable_Body (Id : Entity_Id) is
      Save_In_Elab    : constant Boolean := Inside_Elaboration;
      Saved_Env       : Perm_Env;
      Saved_Borrowers : Variable_Mapping;
      Saved_Observers : Variable_Mapping;

   begin
      Inside_Elaboration := False;
      pragma Assert (No (Current_Subp));
      Current_Subp := Id;

      --  Save environment and put a new one in place

      Move_Env (Current_Perm_Env, Saved_Env);
      Move_Variable_Mapping (Current_Borrowers, Saved_Borrowers);
      Move_Variable_Mapping (Current_Observers, Saved_Observers);

      --  Add formals and globals to the environment with adequate permissions

      if Is_Subprogram_Or_Entry (Id) or else Is_Task_Type (Id) then
         if Is_Subprogram_Or_Entry (Id) then
            Setup_Parameters (Id);
         end if;
         Setup_Globals (Id);
      end if;

      --  For operations directly inside protected objects, add protected
      --  components to the environment with adequate permissions.

      if Ekind (Scope (Id)) = E_Protected_Type then
         Setup_Protected_Components (Id);
      end if;

      --  Analyze the body of the subprogram. For expression function,
      --  do not use the body which might not have been marked. Instead,
      --  get the expression and simulate a single return statement.

      if Is_Expression_Function_Or_Completion (Id) then
         declare
            Expr : constant Node_Id :=
              Expression (Get_Expression_Function (Id));

         begin
            Check_Simple_Return_Expression (Expr, Id);
            Return_Globals (Id);
         end;
      else
         declare
            Body_N : constant Node_Id := Get_Body (Id);
         begin
            Check_List (Declarations (Body_N));

            if Ekind (Id) in Subprogram_Kind | Entry_Kind | Task_Kind then
               Check_Node (Handled_Statement_Sequence (Body_N));
            end if;

            Check_End_Of_Scope (Declarations (Body_N));
         end;
      end if;

      --  Check the read-write permissions of borrowed parameters/globals

      if Is_Entry (Id)
        or else (Ekind (Id) = E_Procedure and then not No_Return (Id))
      then
         Return_Parameters (Id);
         Return_Globals (Id);

         --  For operations directly inside protected objects, check the
         --  permission of protected components on return.

         if Ekind (Scope (Id)) = E_Protected_Type then
            Return_Protected_Components (Id);
         end if;
      end if;

      --  Restore the saved environment and free the current one

      Move_Env (Saved_Env, Current_Perm_Env);
      Move_Variable_Mapping (Saved_Borrowers, Current_Borrowers);
      Move_Variable_Mapping (Saved_Observers, Current_Observers);

      Inside_Elaboration := Save_In_Elab;
      Current_Subp := Empty;
   end Check_Callable_Body;

   -----------------------
   -- Check_Declaration --
   -----------------------

   procedure Check_Declaration (Decl : Node_Id) is
      Target : constant Entity_Id := Defining_Identifier (Decl);
      Expr   : Node_Id;

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
               Check_Assignment (Target => Target, Expr => Expr);
            end if;

            --  Always add variable to the current permission environment,
            --  even in the illegal case, as the rest of the analysis expects
            --  to find it.

            Setup_Environment_For_Object
              (Target,
               (if Is_Read_Only (Target) then Read_Only else Read_Write),
               Decl);

         --  Checking should not be called directly on these nodes

         when N_Function_Specification
            | N_Entry_Declaration
            | N_Procedure_Specification
            | N_Component_Declaration
            | N_Iterator_Specification
            | N_Loop_Parameter_Specification
         =>
            raise Program_Error;

         --  Ignored constructs for pointer checking

         when N_Formal_Object_Declaration
            | N_Formal_Package_Declaration
            | N_Formal_Type_Declaration
            | N_Incomplete_Type_Declaration
            | N_Private_Extension_Declaration
            | N_Private_Type_Declaration
            | N_Protected_Type_Declaration
            | N_Exception_Declaration
         =>
            null;

         --  The following nodes are rewritten by semantic analysis

         when N_Expression_Function =>
            raise Program_Error;
      end case;
   end Check_Declaration;

   ------------------------
   -- Check_End_Of_Scope --
   ------------------------

   procedure Check_End_Of_Scope (Decls : List_Id; N : Node_Id := Empty) is
      Decl     : Node_Id;
      Obj, Typ : Entity_Id;
   begin
      Decl := First (Decls);
      while Present (Decl) loop

         if Nkind (Decl) = N_Object_Declaration then
            Obj := Defining_Identifier (Decl);
            Typ := Etype (Obj);

            --  Check that local borrowers are in the Unrestricted state

            if Is_Anonymous_Access_Object_Type (Typ)
              and then not Is_Access_Constant (Typ)
            then
               declare
                  E_Obj     : constant Expr_Or_Ent :=
                    (Is_Ent => True, Ent => Obj, Loc => Decl);
                  Perm_Expl : constant Perm_And_Expl :=
                    Get_Perm_And_Expl (E_Obj);
               begin
                  if Perm_Expl.Perm /= Read_Write then
                     Perm_Error_Borrow_End
                       (E          => Obj,
                        N          => (if Present (N) then N else Obj),
                        Found_Perm => Perm_Expl.Perm,
                        Expl       => Perm_Expl.Expl);
                  end if;
               end;
            end if;
         end if;

         Next (Decl);
      end loop;
   end Check_End_Of_Scope;

   ------------------
   -- Check_Entity --
   ------------------

   procedure Check_Entity (E : Entity_Id) is

   begin
      Reset (Default_Perm_Env);
      Reset (Current_Perm_Env);
      pragma Assert (Object_Scope.Is_Initial_Value);
      Object_Scope.Push_Scope;
      case Ekind (E) is
         when Type_Kind =>
            if Ekind (E) in E_Task_Type | E_Protected_Type
              and then Entity_Body_In_SPARK (E)
            then
               Check_Callable_Body (E);
            end if;

         when Object_Kind =>

            null;

         when E_Entry | E_Function | E_Procedure =>
            if Entity_Body_In_SPARK (E) then
               Check_Callable_Body (E);
            end if;

         when E_Package =>
            declare
               Scope : constant Opt_Unit_Kind_Id :=
                 (if Is_Compilation_Unit (E)
                  then Empty
                  else Enclosing_Unit (E));

            begin
               --  Only check a package entity if its enclosing unit is not
               --  already checked. Otherwise, E will be checked in the
               --  context of its scope.

               if Present (Scope) and then Entity_Spec_In_SPARK (Scope) then
                  pragma
                    Assert (for some E of Entities_To_Translate => E = Scope);
               else
                  pragma
                    Assert (for all E of Entities_To_Translate => E /= Scope);
                  Check_Package_Entity (E);
               end if;
            end;

         when E_Loop =>
            null;

         when others =>
            raise Program_Error;
      end case;
      Object_Scope.Pop_Scope;

   end Check_Entity;

   -----------------------
   -- Check_Expr_Or_Ent --
   -----------------------

   procedure Check_Expr_Or_Ent
     (Expr : Expr_Or_Ent; Mode : Extended_Checking_Mode) is
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

   procedure Check_Expression (Expr : Node_Id; Mode : Extended_Checking_Mode)
   is
      --  Local subprograms

      procedure Check_Anonymous_Object (Expr : Node_Id; Mode : Checking_Mode);
      --  Read or move an anonymous object

      procedure Check_At_End_Borrow_Call (Expr : Node_Id);
      --  Check that the parameter of a function annotated with At_End_Borrow
      --  is rooted at a borrowed expression or at a borrower. Also fill
      --  the At_End_Borrow map.

      function Is_Type_Name (Expr : Node_Id) return Boolean;
      --  Detect when a path expression is in fact a type name

      procedure Read_Expression (Expr : Node_Id);
      --  Most subexpressions are only analyzed in Read mode. This is a
      --  specialized version of Check_Expression for that case.

      procedure Read_Expression_List (L : List_Id);
      --  Call Read_Expression on every expression in the list L

      procedure Read_Indexes (Expr : Node_Id);
      --  When processing a path, the index expressions and function call
      --  arguments occurring on the path should be analyzed in Read mode.

      ----------------------------
      -- Check_Anonymous_Object --
      ----------------------------

      procedure Check_Anonymous_Object (Expr : Node_Id; Mode : Checking_Mode)
      is
         --  Local subprograms

         procedure Check_Associations (Assocs : List_Id);
         --  Check all associations of an aggregate

         procedure Check_Expressions (Expressions : List_Id);
         --  Check all expressions of an aggregate

         procedure Check_Subobject (Expr : Node_Id);
         --  Check a subobject, passing on the toplevel Mode if it is an object
         --  or forcing Read mode otherwise.

         ------------------------
         -- Check_Associations --
         ------------------------

         procedure Check_Associations (Assocs : List_Id) is

            procedure Read_Choice (Choice : Node_Id);
            --  Read all indexes in a (possibly deep) choice

            procedure Read_Choice (Choice : Node_Id) is
               Pref : Node_Id := Choice;
            begin
               if Nkind (Choice) = N_Aggregate then
                  --  Deal with special choices of multi-dimensional 'Update
                  --  attribute for arrays

                  Pref := First (Expressions (Choice));
                  while Present (Pref) loop
                     Read_Expression (Pref);
                     Next (Pref);
                  end loop;

                  return;
               end if;

               if Is_Deep_Choice (Choice, Etype (Expr)) then
                  while not Is_Root_Prefix_Of_Deep_Choice (Pref) loop
                     if Nkind (Pref) = N_Indexed_Component then
                        Read_Expression_List (Expressions (Pref));
                     end if;
                     Pref := Prefix (Pref);
                  end loop;
               end if;

               if Is_Array_Type (Etype (Expr)) then
                  Read_Expression (Pref);
               end if;
            end Read_Choice;

            CL     : List_Id;
            Assoc  : Node_Id := Nlists.First (Assocs);
            Choice : Node_Id;

         begin
            while Present (Assoc) loop
               CL := Choice_List (Assoc);

               --  We should also check that the expressions used in choices
               --  of array aggregates are readable.

               Choice := Nlists.First (CL);
               while Present (Choice) loop
                  if Nkind (Choice) /= N_Others_Choice then
                     Read_Choice (Choice);
                  end if;
                  Next (Choice);
               end loop;

               --  The subexpressions of an aggregate are read or moved as part
               --  of the implicit assignments.

               if not Box_Present (Assoc) then
                  Check_Subobject (Expression (Assoc));
               end if;

               Next (Assoc);
            end loop;
         end Check_Associations;

         -----------------------
         -- Check_Expressions --
         -----------------------

         procedure Check_Expressions (Expressions : List_Id) is
            N : Node_Id;
         begin
            N := First (Expressions);
            while Present (N) loop
               Check_Subobject (N);
               Next (N);
            end loop;
         end Check_Expressions;

         ---------------------
         -- Check_Subobject --
         ---------------------

         procedure Check_Subobject (Expr : Node_Id) is
            Sub_Mode : constant Checking_Mode :=
              (if Is_Path_Expression (Expr) then Mode else Read);
         begin
            Check_Expression (Expr, Sub_Mode);
         end Check_Subobject;

         --  Start of processing for Check_Anonymous_Object

      begin
         pragma Assert (Is_Path_Expression (Expr));

         --  The cases considered below should correspond to those in
         --  Collect_Moved_Objects in gnat2why-expr.adb

         case N_Subexpr'(Nkind (Expr)) is

            when N_Qualified_Expression
               | N_Type_Conversion
               | N_Unchecked_Type_Conversion
            =>
               Check_Anonymous_Object (Expression (Expr), Mode);

            --  The argument of an allocator is read or moved as part of the
            --  implicit assignment.

            when N_Allocator =>
               Check_Subobject (Expression (Expr));

            when N_Aggregate =>

               --  Container aggregates should be treated as function calls

               if not Is_Container_Aggregate (Expr) then
                  Check_Expressions (Expressions (Expr));
                  Check_Associations (Component_Associations (Expr));
               end if;

            when N_Delta_Aggregate =>
               Check_Subobject (Expression (Expr));
               Check_Associations (Component_Associations (Expr));

            when N_Extension_Aggregate =>
               Check_Subobject (Ancestor_Part (Expr));
               Check_Expressions (Expressions (Expr));
               Check_Associations (Component_Associations (Expr));

            --  Handle 'Update like delta aggregate

            when N_Attribute_Reference =>
               if Get_Attribute_Id (Attribute_Name (Expr)) = Attribute_Update
               then
                  Check_Subobject (Prefix (Expr));
                  Check_Expressions (Expressions (Expr));
               end if;

            when others =>
               null;
         end case;
      end Check_Anonymous_Object;

      ------------------------------
      -- Check_At_End_Borrow_Call --
      ------------------------------

      procedure Check_At_End_Borrow_Call (Expr : Node_Id) is
         Actual : constant Node_Id := First_Actual (Expr);
         Root   : constant Entity_Id := Get_Root_Object (Actual);
         Key    : Variable_Maps.Key_Option;
         Brower : Entity_Id := Empty;
         Vars   : Flow_Id_Sets.Set := Get_Variables_For_Proof (Expr, Expr);

      begin
         --  Check that the call does not depend on any variable but its root.
         --  ??? Should it be moved to flow analysis?

         Vars.Delete (Direct_Mapping_Id (Root));
         for Obj of Vars loop
            if Obj.Kind /= Direct_Mapping or else Is_Mutable_In_Why (Obj.Node)
            then
               BC_Error
                 (Create
                    ("actual for a call to a function annotated with"
                     & " At_End_Borrow should not depend on a variable"),
                  Actual);
               return;
            end if;
         end loop;

         --  Go through the set of borrowers. Try to find either a
         --  borrowed expression which is almost a prefix of Actual or
         --  a borrower which is the root of the path. If we have both,
         --  we want to consider the borrowed expression.

         if No (Brower) then
            Key := Get_First_Key (Current_Borrowers);
            while Key.Present loop

               --  Root is a local borrower. Keep searching in case Expr is
               --  also a borrowed expression.

               if Key.K = Root then
                  Brower := Root;

               --  A prefix of Expr is a borrowed expression. It cannot be the
               --  prefix of any other borrowed expression, stop the search
               --  here.

               else
                  declare
                     Borrowed_Bag : constant Node_Vectors.Vector :=
                       Get (Current_Borrowers, Key.K);
                  begin
                     --  A borrower may have only one borrowed path

                     pragma Assert (Borrowed_Bag.Length = 1);
                     if Is_Prefix_Or_Almost
                          (Pref => Borrowed_Bag.First_Element, Expr => +Actual)
                     then
                        Brower := Key.K;
                        exit;
                     end if;
                  end;
               end if;

               Key := Get_Next_Key (Current_Borrowers);
            end loop;
         end if;

         --  Inside traversal functions, constant borrowers are handled as
         --  observers. Search similarly in the observers map.

         if No (Brower) then
            Key := Get_First_Key (Current_Observers);
            while Key.Present loop

               --  Only search for keys which are actually borrowers

               if Is_Access_Constant (Etype (Key.K)) then
                  null;

               --  Root is a local borrower. Keep searching in case Expr is
               --  also a borrowed expression.

               elsif Key.K = Root then
                  Brower := Root;

               --  A prefix of Expr is a borrowed expression. It cannot be the
               --  prefix of any other borrowed expression, stop the search
               --  here.

               else
                  declare
                     Borrowed_Bag : constant Node_Vectors.Vector :=
                       Get (Current_Observers, Key.K);
                  begin
                     --  A borrower may have only one borrowed path

                     pragma Assert (Borrowed_Bag.Length = 1);
                     if Is_Prefix_Or_Almost
                          (Pref => Borrowed_Bag.First_Element, Expr => +Actual)
                     then
                        Brower := Key.K;
                        exit;
                     end if;
                  end;
               end if;

               Key := Get_Next_Key (Current_Observers);
            end loop;
         end if;

         if No (Brower) then
            BC_Error
              (Create
                 ("actual for a call to a function annotated with"
                  & " At_End_Borrow should be rooted at a borrower or a"
                  & " borrowed expression"),
               Actual);
         else
            Set_At_End_Borrow_Call (Expr, Brower);
         end if;
      end Check_At_End_Borrow_Call;

      ------------------
      -- Is_Type_Name --
      ------------------

      function Is_Type_Name (Expr : Node_Id) return Boolean is
      begin
         return
           Nkind (Expr) in N_Expanded_Name | N_Identifier
           and then Is_Type (Entity (Expr));
      end Is_Type_Name;

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
            Check_Expression (N, Read);
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

         procedure Read_Protected_Components
           (Subp : Entity_Id; Call : Node_Id);
         --  Read the implicit parameter of an internal call to a protected
         --  function.

         ----------------
         -- Read_Param --
         ----------------

         procedure Read_Param (Formal : Entity_Id; Actual : Node_Id) is
            pragma Unreferenced (Formal);
         begin
            Read_Expression (Actual);
         end Read_Param;

         -------------------------------
         -- Read_Protected_Components --
         -------------------------------

         procedure Read_Protected_Components (Subp : Entity_Id; Call : Node_Id)
         is
            procedure Read_Component (Comp : Entity_Id);
            --  Read component of protected object

            --------------------
            -- Read_Component --
            --------------------

            procedure Read_Component (Comp : Entity_Id) is
            begin
               Check_Parameter_Or_Global
                 (Expr       => (Is_Ent => True, Ent => Comp, Loc => Call),
                  Param      => Comp,
                  Typ        => Etype (Comp),
                  Kind       => E_In_Parameter,
                  Subp       => Subp,
                  Global_Var => False);
            end Read_Component;

            --  Local variables
            Typ : constant Entity_Id := Scope (Subp);
         begin
            --  The protected object is an implicit input of protected
            --  functions.
            pragma Assert (Ekind (Subp) = E_Function);

            declare
               Comp : Entity_Id := First_Component_Or_Discriminant (Typ);
            begin
               while Present (Comp) loop
                  Read_Component (Comp);
                  Next_Component_Or_Discriminant (Comp);
               end loop;
            end;

            declare
               Anon_Obj : constant Entity_Id :=
                 Anonymous_Object (Scope (Subp));
            begin
               if Present (Anon_Obj) then
                  for Comp of Iter (Part_Of_Constituents (Anon_Obj)) loop
                     Read_Component (Comp);
                  end loop;
               end if;
            end;
         end Read_Protected_Components;

         procedure Read_Params is new Iterate_Call_Parameters (Read_Param);

         --  Start of processing for Read_Indexes

      begin
         pragma Assert (Is_Path_Expression (Expr));

         case N_Subexpr'(Nkind (Expr)) is
            when N_Identifier | N_Expanded_Name | N_Null =>
               null;

            when N_Allocator
               | N_Aggregate
               | N_Delta_Aggregate
               | N_Extension_Aggregate
            =>
               Check_Anonymous_Object (Expr, Read);

            when N_Explicit_Dereference | N_Selected_Component =>
               Read_Indexes (Prefix (Expr));

            when N_Indexed_Component =>
               Read_Indexes (Prefix (Expr));
               Read_Expression_List (Expressions (Expr));

            when N_Slice =>
               Read_Indexes (Prefix (Expr));
               Read_Expression (Discrete_Range (Expr));

            when N_Function_Call =>
               declare
                  Fun : constant Entity_Id := Get_Called_Entity (Expr);

               begin
                  --  Ignore predicate function calls if the entity is not in
                  --  SPARK.

                  if Ekind (Fun) = E_Function
                    and then Is_Predicate_Function (Fun)
                    and then not Entity_In_SPARK (Fun)
                  then
                     return;
                  end if;

                  --  If the called entity is annotated with At_End_Borrow,
                  --  check that its parameter is rooted at a borrowed
                  --  expression or at a borrower.

                  if Has_At_End_Borrow_Annotation (Fun) then
                     Check_At_End_Borrow_Call (Expr);
                  end if;

                  Read_Params (Expr);
                  Check_Globals (Fun, Expr);

                  --  For operations directly inside protected objects, check
                  --  the permission of protected components on internal calls.

                  if Ekind (Scope (Fun)) = E_Protected_Type
                    and then not Is_External_Call (Expr)
                  then
                     Read_Protected_Components (Fun, Expr);
                  end if;
               end;

            when N_Qualified_Expression
               | N_Type_Conversion
               | N_Unchecked_Type_Conversion
            =>
               Read_Indexes (Expression (Expr));

            when N_Attribute_Reference =>
               pragma
                 Assert
                   (Get_Attribute_Id (Attribute_Name (Expr))
                    in Attribute_Loop_Entry
                     | Attribute_Update
                     | Attribute_Image
                     | Attribute_Img
                     | Attribute_First
                     | Attribute_Last
                     | Attribute_Length
                     | Attribute_Access);

               if Get_Attribute_Id (Attribute_Name (Expr))
                  in Attribute_First
                   | Attribute_Last
                   | Attribute_Length
                   | Attribute_Access
               then
                  Read_Indexes (Prefix (Expr));
               else
                  Read_Expression (Prefix (Expr));
                  Read_Expression_List (Expressions (Expr));
               end if;

            when N_Op_Eq | N_Op_Ne =>
               Read_Indexes (Left_Opnd (Expr));
               Read_Indexes (Right_Opnd (Expr));

            when others =>
               raise Program_Error;
         end case;
      end Read_Indexes;

      --  Start of processing for Check_Expression

   begin
      if Is_Type_Name (Expr) then
         return;

      elsif Expr in N_Subexpr_Id and then Is_Path_Expression (Expr) then
         if Mode /= Assign then
            Read_Indexes (Expr);
         end if;

         if Mode /= Read_Subexpr then
            --  As Process_Path only deals with named paths, deal here with
            --  anonymous objects created by allocators and aggregates.

            if No (Get_Root_Object (Expr)) then
               Check_Anonymous_Object (Expr, Mode);
            else
               Process_Path (+Expr, Mode);
            end if;
         end if;

         return;
      end if;

      --  Expressions that are not path expressions should only be analyzed in
      --  Read mode, with exception of conditional path expressions which may
      --  be in observe.

      pragma Assert (Mode in Read | Observe);
      pragma
        Assert
          (if Mode = Observe
             then Nkind (Expr) in N_If_Expression | N_Case_Expression);

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

         when N_Binary_Op | N_Short_Circuit =>
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

                  when Attribute_Access
                     | Attribute_Address
                     | Attribute_Alignment
                     | Attribute_Bit_Order
                     | Attribute_Callable
                     | Attribute_Component_Size
                     | Attribute_Constrained
                     | Attribute_First
                     | Attribute_First_Bit
                     | Attribute_Initialized
                     | Attribute_Last
                     | Attribute_Last_Bit
                     | Attribute_Length
                     | Attribute_Modulus
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
                     | Attribute_Copy_Sign
                     | Attribute_Enum_Rep
                     | Attribute_Enum_Val
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

                  when Attribute_Image | Attribute_Img =>
                     if No (Args) then
                        Read_Expression (Pref);
                     else
                        Read_Expression_List (Args);
                     end if;

                  --  The following attributes apply to types; there are no
                  --  expressions to read.

                  when Attribute_Class | Attribute_Storage_Size =>
                     null;

                  --  Postconditions should not be analyzed. Attributes Update,
                  --  Old and Loop_Entry correspond to paths which are handled
                  --  previously.

                  when Attribute_Loop_Entry
                     | Attribute_Old
                     | Attribute_Result
                     | Attribute_Update
                  =>
                     raise Program_Error;

                  --  Other attributes are not supported in SPARK (or only for
                  --  static values), leading to an error in marking. Ignore
                  --  them here.

                  when others =>
                     null;
               end case;
            end;

         when N_Range =>
            Read_Expression (Low_Bound (Expr));
            Read_Expression (High_Bound (Expr));

         when N_If_Expression =>
            declare
               Cond_Expr : constant Node_Id := First (Expressions (Expr));
               Then_Expr : constant Node_Id := Next (Cond_Expr);
               Else_Expr : constant Node_Id := Next (Then_Expr);
            begin
               Read_Expression (Cond_Expr);
               Check_Expression (Then_Expr, Mode);
               Check_Expression (Else_Expr, Mode);
            end;

         when N_Case_Expression =>
            declare
               Cases    : constant List_Id := Alternatives (Expr);
               Cur_Case : Node_Id := First (Cases);

            begin
               while Present (Cur_Case) loop
                  Check_Expression (Expression (Cur_Case), Mode);
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
            Object_Scope.Push_Scope;
            declare
               For_In_Spec     : constant Node_Id :=
                 Loop_Parameter_Specification (Expr);
               For_Of_Spec     : constant Node_Id :=
                 Iterator_Specification (Expr);
               For_Of_Spec_Typ : Node_Id;
               For_Actual_Spec : constant Node_Id :=
                 (if Present (For_In_Spec) then For_In_Spec else For_Of_Spec);
               Quantified_Var  : constant Entity_Id :=
                 Defining_Identifier (For_Actual_Spec);

            begin
               --  Temporarily add the quantified variable to the permission
               --  environment, so that context for sub-expressions remain
               --  well-formed.

               Setup_Environment_For_Object
                 (Quantified_Var, Read_Only, For_Actual_Spec);

               --  Sub-expressions checking

               if Present (For_In_Spec) then
                  Read_Expression (Discrete_Subtype_Definition (For_In_Spec));
                  if Present (Iterator_Filter (For_In_Spec)) then
                     Read_Expression (Iterator_Filter (For_In_Spec));
                  end if;
               else
                  Read_Expression (Name (For_Of_Spec));
                  For_Of_Spec_Typ := Subtype_Indication (For_Of_Spec);
                  if Present (For_Of_Spec_Typ) then
                     Read_Expression (For_Of_Spec_Typ);
                  end if;

                  if Present (Iterator_Filter (For_Of_Spec)) then
                     Read_Expression (Iterator_Filter (For_Of_Spec));
                  end if;
               end if;

               Read_Expression (Condition (Expr));
            end;
            Object_Scope.Pop_Scope;

         when N_Character_Literal
            | N_Numeric_Or_String_Literal
            | N_Operator_Symbol
            | N_Raise_Expression
            | N_Raise_xxx_Error
         =>
            null;

         when N_Delta_Aggregate | N_Target_Name =>
            null;

         when N_Explicit_Dereference | N_Selected_Component =>
            Check_Expression (Prefix (Expr), Mode);

         when N_Indexed_Component =>
            Check_Expression (Prefix (Expr), Mode);
            Read_Expression_List (Expressions (Expr));

         when N_Slice =>
            Check_Expression (Prefix (Expr), Mode);
            Read_Expression (Discrete_Range (Expr));

         when N_Expression_With_Actions =>

            --  Go over the objects declared in a declare expressions and fill
            --  the map for them. No need to handle local borrowers or
            --  observers which are not allowed.

            Object_Scope.Push_Scope;
            Check_List (Actions (Expr));
            Check_Expression (Expression (Expr), Mode);
            Object_Scope.Pop_Scope;

         --  Procedure calls are handled in Check_Node

         when N_Procedure_Call_Statement =>
            raise Program_Error;

         --  Path expressions are handled before this point

         when N_Aggregate
            | N_Allocator
            | N_Expanded_Name
            | N_Extension_Aggregate
            | N_Function_Call
            | N_Identifier
            | N_Null
            | N_External_Initializer
         =>
            raise Program_Error;

         --  The following nodes are never generated in GNATprove mode

         when N_Reference =>
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
        (Exiting_Env : Perm_Env; Entry_Env : Perm_Env);
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
         Loop_Stmt  : Node_Id;
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
        (Exiting_Env : Perm_Env; Entry_Env : Perm_Env)
      is
         Comp_Entry : Perm_Tree_Maps.Key_Option;

         procedure Do_Check (Key_Opt : Perm_Tree_Maps.Key_Option)
         with Pre => Key_Opt.Present;
         --  Loop body, do the check on one key. Split out because the loop
         --  is split in two parts.

         procedure Do_Check (Key_Opt : Perm_Tree_Maps.Key_Option) is
            Iter_Entry : constant not null Perm_Tree_Access :=
              Query_Read_Only_Tree (Entry_Env, Key_Opt.K);
            Iter_Exit  : constant not null Perm_Tree_Access :=
              Query_Read_Only_Tree (Exiting_Env, Key_Opt.K);
         begin
            Check_Is_Less_Restrictive_Tree
              (New_Tree  => Iter_Exit,
               Orig_Tree => Iter_Entry,
               E         => Comp_Entry.K);
         end Do_Check;

         --  Start of processing for Check_Is_Less_Restrictive_Env

      begin
         --  There is no guarantee the set of keys actually in any of the
         --  environment is a subset of the other, so we need to iterate both.
         --  For keys that are in neither, the matching permissions are both
         --  that of the default environment, hence are guaranteed to match.

         Comp_Entry := Get_First_Key (Entry_Env);
         while Comp_Entry.Present loop
            Do_Check (Comp_Entry);
            Comp_Entry := Get_Next_Key (Entry_Env);
         end loop;

         Comp_Entry := Get_First_Key (Exiting_Env);
         while Comp_Entry.Present loop

            --  Prevent duplicated iteration

            if Get (Entry_Env, Comp_Entry.K) = null then
               Do_Check (Comp_Entry);
            end if;

            Comp_Entry := Get_Next_Key (Exiting_Env);
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
           (Tree : Perm_Tree_Access; Perm : Perm_Kind; E : Entity_Id);
         --  Auxiliary procedure to check that Tree is less restrictive than
         --  the given permission Perm.

         procedure Check_Is_More_Restrictive_Tree_Than
           (Tree : Perm_Tree_Access; Perm : Perm_Kind; E : Entity_Id);
         --  Auxiliary procedure to check that Tree is more restrictive than
         --  the given permission Perm.

         -----------------------------------------
         -- Check_Is_Less_Restrictive_Tree_Than --
         -----------------------------------------

         procedure Check_Is_Less_Restrictive_Tree_Than
           (Tree : Perm_Tree_Access; Perm : Perm_Kind; E : Entity_Id) is
         begin
            if Permission (Tree) < Perm then
               Perm_Error_Loop_Exit
                 (E, Stmt, Permission (Tree), Perm, Explanation (Tree));
            end if;

            case Kind (Tree) is
               when Entire_Object =>
                  if Children_Permission (Tree) < Perm then
                     Perm_Error_Loop_Exit
                       (E,
                        Stmt,
                        Children_Permission (Tree),
                        Perm,
                        Explanation (Tree));
                  end if;

               when Reference =>
                  if Null_Permission (Tree) < Perm then
                     Perm_Error_Loop_Exit
                       (E,
                        Stmt,
                        Null_Permission (Tree),
                        Perm,
                        Explanation (Tree));
                  end if;

                  Check_Is_Less_Restrictive_Tree_Than
                    (Get_All (Tree), Perm, E);

               when Array_Component =>
                  if Bounds_Permission (Tree) < Perm then
                     Perm_Error_Loop_Exit
                       (E,
                        Stmt,
                        Bounds_Permission (Tree),
                        Perm,
                        Explanation (Tree));
                  end if;

                  Check_Is_Less_Restrictive_Tree_Than
                    (Get_Elem (Tree), Perm, E);

               when Record_Component =>
                  declare
                     Comp : Perm_Tree_Access;
                  begin
                     Comp := Perm_Tree_Maps.Get_First (Component (Tree));
                     while Comp /= null loop
                        Check_Is_Less_Restrictive_Tree_Than (Comp, Perm, E);
                        Comp := Perm_Tree_Maps.Get_Next (Component (Tree));
                     end loop;
                  end;
            end case;
         end Check_Is_Less_Restrictive_Tree_Than;

         -----------------------------------------
         -- Check_Is_More_Restrictive_Tree_Than --
         -----------------------------------------

         procedure Check_Is_More_Restrictive_Tree_Than
           (Tree : Perm_Tree_Access; Perm : Perm_Kind; E : Entity_Id) is
         begin
            if Perm < Permission (Tree) then
               Perm_Error_Loop_Exit
                 (E, Stmt, Permission (Tree), Perm, Explanation (Tree));
            end if;

            case Kind (Tree) is
               when Entire_Object =>
                  if Perm < Children_Permission (Tree) then
                     Perm_Error_Loop_Exit
                       (E,
                        Stmt,
                        Children_Permission (Tree),
                        Perm,
                        Explanation (Tree));
                  end if;

               when Reference =>
                  if Perm < Null_Permission (Tree) then
                     Perm_Error_Loop_Exit
                       (E,
                        Stmt,
                        Null_Permission (Tree),
                        Perm,
                        Explanation (Tree));
                  end if;

                  Check_Is_More_Restrictive_Tree_Than
                    (Get_All (Tree), Perm, E);

               when Array_Component =>
                  if Perm < Bounds_Permission (Tree) then
                     Perm_Error_Loop_Exit
                       (E,
                        Stmt,
                        Bounds_Permission (Tree),
                        Perm,
                        Explanation (Tree));
                  end if;

                  Check_Is_More_Restrictive_Tree_Than
                    (Get_Elem (Tree), Perm, E);

               when Record_Component =>
                  declare
                     Comp : Perm_Tree_Access;
                  begin
                     Comp := Perm_Tree_Maps.Get_First (Component (Tree));
                     while Comp /= null loop
                        Check_Is_More_Restrictive_Tree_Than (Comp, Perm, E);
                        Comp := Perm_Tree_Maps.Get_Next (Component (Tree));
                     end loop;
                  end;
            end case;
         end Check_Is_More_Restrictive_Tree_Than;

         --  Start of processing for Check_Is_Less_Restrictive_Tree

      begin
         if Permission (New_Tree) < Permission (Orig_Tree) then
            Perm_Error_Loop_Exit
              (E          => E,
               Loop_Stmt  => Stmt,
               Perm       => Permission (Orig_Tree),
               Found_Perm => Permission (New_Tree),
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
                     if Children_Permission (New_Tree)
                       < Children_Permission (Orig_Tree)
                     then
                        Perm_Error_Loop_Exit
                          (E,
                           Stmt,
                           Perm       => Children_Permission (Orig_Tree),
                           Found_Perm => Children_Permission (New_Tree),
                           Expl       => Explanation (New_Tree));
                     end if;

                  when Reference =>
                     if Children_Permission (New_Tree)
                       < Null_Permission (Orig_Tree)
                     then
                        Perm_Error_Loop_Exit
                          (E,
                           Stmt,
                           Perm       => Null_Permission (Orig_Tree),
                           Found_Perm => Children_Permission (New_Tree),
                           Expl       => Explanation (New_Tree));
                     end if;

                     Check_Is_More_Restrictive_Tree_Than
                       (Get_All (Orig_Tree),
                        Children_Permission (New_Tree),
                        E);

                  when Array_Component =>
                     if Children_Permission (New_Tree)
                       < Bounds_Permission (Orig_Tree)
                     then
                        Perm_Error_Loop_Exit
                          (E,
                           Stmt,
                           Perm       => Bounds_Permission (Orig_Tree),
                           Found_Perm => Children_Permission (New_Tree),
                           Expl       => Explanation (New_Tree));
                     end if;

                     Check_Is_More_Restrictive_Tree_Than
                       (Get_Elem (Orig_Tree),
                        Children_Permission (New_Tree),
                        E);

                  when Record_Component =>
                     declare
                        Comp : Perm_Tree_Access;
                     begin
                        Comp :=
                          Perm_Tree_Maps.Get_First (Component (Orig_Tree));
                        while Comp /= null loop
                           Check_Is_More_Restrictive_Tree_Than
                             (Comp, Children_Permission (New_Tree), E);
                           Comp :=
                             Perm_Tree_Maps.Get_Next (Component (Orig_Tree));
                        end loop;
                     end;
               end case;

            when Reference =>
               case Kind (Orig_Tree) is
                  when Entire_Object =>
                     if Null_Permission (New_Tree)
                       < Children_Permission (Orig_Tree)
                     then
                        Perm_Error_Loop_Exit
                          (E,
                           Stmt,
                           Perm       => Children_Permission (Orig_Tree),
                           Found_Perm => Null_Permission (New_Tree),
                           Expl       => Explanation (New_Tree));
                     end if;

                     Check_Is_Less_Restrictive_Tree_Than
                       (Get_All (New_Tree),
                        Children_Permission (Orig_Tree),
                        E);

                  when Reference =>
                     if Null_Permission (New_Tree)
                       < Null_Permission (Orig_Tree)
                     then
                        Perm_Error_Loop_Exit
                          (E,
                           Stmt,
                           Perm       => Null_Permission (Orig_Tree),
                           Found_Perm => Null_Permission (New_Tree),
                           Expl       => Explanation (New_Tree));
                     end if;

                     Check_Is_Less_Restrictive_Tree
                       (Get_All (New_Tree), Get_All (Orig_Tree), E);

                  when others =>
                     raise Program_Error;
               end case;

            when Array_Component =>
               case Kind (Orig_Tree) is
                  when Entire_Object =>
                     if Bounds_Permission (New_Tree)
                       < Children_Permission (Orig_Tree)
                     then
                        Perm_Error_Loop_Exit
                          (E,
                           Stmt,
                           Perm       => Children_Permission (Orig_Tree),
                           Found_Perm => Bounds_Permission (New_Tree),
                           Expl       => Explanation (New_Tree));
                     end if;

                     Check_Is_Less_Restrictive_Tree_Than
                       (Get_Elem (New_Tree),
                        Children_Permission (Orig_Tree),
                        E);

                  when Array_Component =>
                     if Bounds_Permission (New_Tree)
                       < Bounds_Permission (Orig_Tree)
                     then
                        Perm_Error_Loop_Exit
                          (E,
                           Stmt,
                           Perm       => Bounds_Permission (Orig_Tree),
                           Found_Perm => Bounds_Permission (New_Tree),
                           Expl       => Explanation (New_Tree));
                     end if;

                     Check_Is_Less_Restrictive_Tree
                       (Get_Elem (New_Tree), Get_Elem (Orig_Tree), E);

                  when others =>
                     raise Program_Error;
               end case;

            when Record_Component =>
               declare
                  CompN : Perm_Tree_Access;
               begin
                  CompN := Perm_Tree_Maps.Get_First (Component (New_Tree));

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
                           KeyO  : Perm_Tree_Maps.Key_Option;
                           CompO : Perm_Tree_Access;
                        begin
                           KeyO :=
                             Perm_Tree_Maps.Get_First_Key
                               (Component (Orig_Tree));
                           while KeyO.Present loop
                              CompN :=
                                Perm_Tree_Maps.Get
                                  (Component (New_Tree), KeyO.K);
                              CompO :=
                                Perm_Tree_Maps.Get
                                  (Component (Orig_Tree), KeyO.K);
                              pragma Assert (CompO /= null);

                              Check_Is_Less_Restrictive_Tree (CompN, CompO, E);

                              KeyO :=
                                Perm_Tree_Maps.Get_Next_Key
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
         Loop_Stmt  : Node_Id;
         Perm       : Perm_Kind;
         Found_Perm : Perm_Kind;
         Expl       : Node_Id)
      is
         Ent : constant Expr_Or_Ent :=
           (Is_Ent => True, Ent => E, Loc => Loop_Stmt);
      begin
         BC_Error
           (Create
              ("loop iteration terminates with moved value for &",
               Names => [E]),
            Loop_Stmt,
            Continuations =>
              [Perm_Mismatch
                 (N        => Ent,
                  Exp_Perm => Perm,
                  Act_Perm => Found_Perm,
                  Expl     => Expl)]);
      end Perm_Error_Loop_Exit;

      --  Local variables

      Loop_Name : constant Entity_Id := Entity (Identifier (Stmt));
      Loop_Env  : Perm_Env;
      Scheme    : constant Node_Id := Iteration_Scheme (Stmt);

      --  Start of processing for Check_Loop_Statement

   begin
      Object_Scope.Push_Scope;

      --  If the loop is not a plain-loop, then it may either never be entered,
      --  or it may be exited after a number of iterations. Hence add the
      --  current permission environment as the initial loop exit environment.
      --  Otherwise, the loop exit environment remains empty until it is
      --  populated by analyzing exit statements.

      pragma Assert (Get (Current_Exit_Accumulators, Loop_Name) = null);
      pragma Assert (Get (Current_Continue_Accumulators, Loop_Name) = null);

      if Present (Iteration_Scheme (Stmt)) then
         declare
            Exit_Env : constant Perm_Env_Access := new Perm_Env;

         begin
            Copy_Env (From => Current_Perm_Env, To => Exit_Env.all);
            Set (Current_Exit_Accumulators, Loop_Name, Exit_Env);
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
               Param_Spec    : constant Node_Id :=
                 Loop_Parameter_Specification (Scheme);
               Iter_Spec     : constant Node_Id :=
                 Iterator_Specification (Scheme);
               Concrete_Spec : constant Node_Id :=
                 (if Present (Param_Spec) then Param_Spec else Iter_Spec);
               Loop_Index    : constant Entity_Id :=
                 Defining_Identifier (Concrete_Spec);
            begin
               Setup_Environment_For_Object
                 (Loop_Index, Read_Only, Concrete_Spec);

               if Present (Param_Spec) then
                  Check_Expression
                    (Discrete_Subtype_Definition (Param_Spec), Read);

                  if Present (Iterator_Filter (Param_Spec)) then
                     Check_Expression (Iterator_Filter (Param_Spec), Read);
                  end if;
               else
                  Check_Expression (Name (Iter_Spec), Read);
                  if Present (Subtype_Indication (Iter_Spec)) then
                     Check_Expression (Subtype_Indication (Iter_Spec), Read);
                  end if;

                  if Present (Iterator_Filter (Iter_Spec)) then
                     Check_Expression (Iterator_Filter (Iter_Spec), Read);
                  end if;
               end if;

            end;
         end if;
      end if;

      Copy_Env (Current_Perm_Env, Loop_Env);

      --  At the end of the iteration, we must merge environment from continue
      --  statements.

      Object_Scope.Push_Scope;
      Check_List (Statements (Stmt));
      Merge_Transfer_Of_Control_Env (Current_Continue_Accumulators, Loop_Name);
      Object_Scope.Pop_Scope;

      --  Check that environment gets less restrictive at end of loop

      Check_Is_Less_Restrictive_Env
        (Exiting_Env => Current_Perm_Env, Entry_Env => Loop_Env);
      Free_Env (Loop_Env);

      --  Set environment to the one for exiting the loop

      declare
         Exit_Env : constant Perm_Env_Access :=
           Get (Current_Exit_Accumulators, Loop_Name);
      begin
         --  In the normal case, Exit_Env is not null and we use it. In the
         --  degraded case of a plain-loop without exit statements, Exit_Env is
         --  null, and the code afterward is dead, so we use a reset
         --  environment.

         if Exit_Env /= null then
            Free_Env (Current_Perm_Env);
            Current_Perm_Env := Exit_Env.all;
            Remove (Current_Exit_Accumulators, Loop_Name);
         else
            Reset_Env (Current_Perm_Env);
         end if;
      end;

      Object_Scope.Pop_Scope;
   end Check_Loop_Statement;

   ----------------
   -- Check_Node --
   ----------------

   procedure Check_Node (N : Node_Id) is
   begin
      case Nkind (N) is
         when N_Declaration =>
            Check_Declaration (N);

         when N_Body_Stub =>
            null;

         when N_Statement_Other_Than_Procedure_Call =>
            Check_Statement (N);

         when N_Procedure_Call_Statement =>
            Check_Call_With_Side_Effects (N);

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

         when N_Entry_Body | N_Task_Body =>
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
            Object_Scope.Push_Scope;
            Check_List (Statements (N));
            Object_Scope.Pop_Scope;

            --  Go over the exception handlers. They start in the environment
            --  accumulated for them if any. Their output environment is merged
            --  back into the current environment.

            declare
               Handlers : constant List_Id := Exception_Handlers (N);
               Handler  : Node_Id;
               Save_Env : Perm_Env := Current_Perm_Env;
            begin
               Handler := First_Non_Pragma (Handlers);
               while Present (Handler) loop
                  declare
                     Handler_Env : constant Perm_Env_Access :=
                       Get (Current_Exc_Accumulators, Handler);
                  begin
                     if Handler_Env /= null then
                        Remove (Current_Exc_Accumulators, Handler);
                        Current_Perm_Env := Handler_Env.all;
                        Object_Scope.Push_Scope;
                        Check_List (Statements (Handler));
                        Object_Scope.Pop_Scope;
                        Merge_Env (Current_Perm_Env, Save_Env, Filter => True);
                     end if;
                  end;
                  Next_Non_Pragma (Handler);
               end loop;
               Current_Perm_Env := Save_Env;
            end;

            --  Go over the statements under finally (if any)

            Object_Scope.Push_Scope;
            Check_List (Finally_Statements (N));
            Object_Scope.Pop_Scope;

         when N_Pragma =>
            Check_Pragma (N);

         when N_Subprogram_Declaration =>
            null;

         --  Attribute references in statement position are not supported in
         --  SPARK and will be rejected by GNATprove.

         when N_Attribute_Reference =>
            null;

         --  When a goto label is reached, we merge the accumulated
         --  environment coming from goto statements mentioning this label in
         --  the current environment.

         when N_Label =>
            Merge_Transfer_Of_Control_Env
              (Current_Goto_Accumulators, Entity (Identifier (N)));

         --  Ignored constructs for pointer checking

         when N_Abstract_Subprogram_Declaration
            | N_At_Clause
            | N_Attribute_Definition_Clause
            | N_Call_Marker
            | N_Delta_Constraint
            | N_Digits_Constraint
            | N_Empty
            | N_Enumeration_Representation_Clause
            | N_Exception_Renaming_Declaration
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
         Borrowed : constant Node_Id := Check_On_Borrowed (Expr);
      begin
         if Present (Borrowed) then
            if Expr.Is_Ent then
               BC_Error
                 (Create
                    ("& was borrowed #",
                     Names         => [Expr.Ent],
                     Secondary_Loc => Sloc (Borrowed)),
                  Expr.Loc);
            else
               BC_Error
                 (Create
                    ("object was borrowed #",
                     Secondary_Loc => Sloc (Borrowed)),
                  Expr.Expr);
            end if;
         end if;
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
         Observed : constant Node_Id := Check_On_Observed (Expr);
      begin
         if Present (Observed) then
            if Expr.Is_Ent then
               BC_Error
                 (Create
                    ("& was observed #",
                     Names         => [Expr.Ent],
                     Secondary_Loc => Sloc (Observed)),
                  Expr.Loc);
            else
               BC_Error
                 (Create
                    ("object was observed #",
                     Secondary_Loc => Sloc (Observed)),
                  Expr.Expr);
            end if;
         end if;
      end;
   end Check_Not_Observed;

   -----------------------
   -- Check_On_Borrowed --
   -----------------------

   function Check_On_Borrowed (Expr : Expr_Or_Ent) return Node_Id is
      Key     : Variable_Maps.Key_Option := Get_First_Key (Current_Borrowers);
      Var     : Entity_Id;
      Current : constant Node_Id :=
        (if not Expr.Is_Ent
         then Get_Observed_Or_Borrowed_Expr (Expr.Expr)
         else Types.Empty);

   begin
      --  For every borrowed object, check that:
      --    * the borrowed expression is not a prefix of Expr
      --    * Expr is not a prefix of the borrowed expression.

      while Key.Present loop
         Var := Key.K;
         for Borrowed of Get (Current_Borrowers, Var) loop
            if Is_Prefix_Or_Almost (Pref => Borrowed, Expr => Expr)
              or else (if Expr.Is_Ent
                       then Get_Root_Object (Borrowed) = Expr.Ent
                       else Is_Prefix_Or_Almost (Current, +Borrowed))
            then
               return Borrowed;
            end if;
         end loop;

         Key := Get_Next_Key (Current_Borrowers);
      end loop;

      return Empty;
   end Check_On_Borrowed;

   -----------------------
   -- Check_On_Observed --
   -----------------------

   function Check_On_Observed (Expr : Expr_Or_Ent) return Node_Id is
      Key     : Variable_Maps.Key_Option := Get_First_Key (Current_Observers);
      Var     : Entity_Id;
      Current : constant Node_Id :=
        (if not Expr.Is_Ent
         then Get_Observed_Or_Borrowed_Expr (Expr.Expr)
         else Types.Empty);

   begin
      --  For every observed object, check that:
      --    * no observed expression is a prefix of Expr
      --    * Expr is not a prefix of any observed expression.

      while Key.Present loop
         Var := Key.K;

         for Observed of Get (Current_Observers, Var) loop
            if Is_Prefix_Or_Almost (Pref => Observed, Expr => Expr)
              or else (if Expr.Is_Ent
                       then Get_Root_Object (Observed) = Expr.Ent
                       else Is_Prefix_Or_Almost (Current, +Observed))
            then
               return Observed;
            end if;

            Key := Get_Next_Key (Current_Observers);
         end loop;
      end loop;

      return Empty;
   end Check_On_Observed;

   ------------------------
   -- Check_Package_Body --
   ------------------------

   procedure Check_Package_Body (Id : Entity_Id) is
      Save_In_Elab : constant Boolean := Inside_Elaboration;
      Body_N       : constant Node_Id := Package_Body (Id);

   begin
      Inside_Elaboration := True;

      --  Check declarations and statements in the special mode for
      --  elaboration.

      if Entity_Body_In_SPARK (Id) then
         Check_List (Declarations (Body_N));

         Check_Node (Handled_Statement_Sequence (Body_N));
      end if;

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

      if Present (Priv_Decls) and then Private_Spec_In_SPARK (Id) then
         Check_List (Private_Declarations (Spec));
      end if;

      Inside_Elaboration := Save_In_Elab;
   end Check_Package_Spec;

   -------------------------------
   -- Check_Parameter_Or_Global --
   -------------------------------

   procedure Check_Parameter_Or_Global
     (Expr       : Expr_Or_Ent;
      Param      : Entity_Id;
      Typ        : Entity_Id;
      Kind       : Formal_Kind;
      Subp       : Entity_Id;
      Global_Var : Boolean)
   is
      Mode : Checking_Mode;

   begin
      case Kind is
         when E_In_Parameter =>

            --  Inputs of functions without side effects have R permission
            --  only. Protected functions are never allowed to modify protected
            --  components.

            --  nested expression exceeds line length
            --!format off
            if Ekind (Subp) = E_Function and then
              (not Is_Function_With_Side_Effects (Subp)
               or else (Within_Protected_Type (Subp)
                        and then Expr.Is_Ent
                        and then Is_Protected_Component_Or_Discr_Or_Part_Of
                                   (Expr.Ent)))
            --!format on
            then
               Mode := Read;

            --  Input global variables have R permission only

            elsif Global_Var then
               Mode := Read;

            --  Anonymous access to constant is an observe

            elsif Is_Anonymous_Access_Object_Type (Typ)
              and then Is_Access_Constant (Typ)
            then
               Mode := Observe;

            --  Other access-to-variable types are a borrow

            elsif Is_Access_Object_Type (Typ)
              and then not Is_Access_Constant (Typ)
            then
               Mode := Borrow;

            --  Deep types other than access types define an observe, with
            --  exception of mutable in parameters

            elsif Is_Deep (Typ) then
               Mode :=
                 (if Has_Mutable_In_Param_Annotation (Param)
                  then Borrow
                  else Observe);

            --  Otherwise the variable is read

            else
               Mode := Read;
            end if;

         when E_Out_Parameter =>
            pragma Assert (not Is_Anonymous_Access_Object_Type (Typ));
            Mode := Assign;

         when E_In_Out_Parameter =>
            if Is_Unchecked_Deallocation_Instance (Subp) then
               Mode := Free;

            --  Anonymous access to constant is an observe

            elsif Is_Anonymous_Access_Object_Type (Typ)
              and then Is_Access_Constant (Typ)
            then
               pragma Assert (Global_Var);
               Mode := Observe;

            --  Other anonymous access-to-object types are a borrow

            elsif Is_Anonymous_Access_Object_Type (Typ) then
               pragma Assert (Global_Var);
               Mode := Borrow;
            else
               Mode := Move;
            end if;
      end case;

      if Mode = Assign then
         Check_Expr_Or_Ent (Expr, Read_Subexpr);
      end if;

      --  SPARK RM 3.10(17): A path rooted at a non-ghost object shall only
      --  be moved, or borrowed, if the target object of the move or borrow
      --  is itself non-ghost.

      if not Global_Var
        and then Mode in Borrow | Free | Move
        and then Is_Ghost_Entity (Subp)
      then
         declare
            Root : constant Entity_Id := Get_Root_Object (Expr.Expr);
         begin
            --  Here, errors should only occur with mode Borrow as Free and
            --  Move are associated with IN OUT parameters that should be
            --  rejected by the frontend.

            if No (Root) then
               null;
            elsif not Is_Ghost_Entity (Root) then
               pragma Assert (Mode = Borrow);
               BC_Error
                 (Create
                    ("non-ghost object & cannot be borrowed"
                     & " in a call to ghost subprogram &",
                     Names => [Root, Subp]),
                  Expr.Expr);

            elsif not Is_Checked_Ghost_Entity (Subp)
              and then Is_Checked_Ghost_Entity (Root)
            then
               pragma Assert (Mode = Borrow);
               BC_Error
                 (Create
                    ("enabled ghost object & cannot be borrowed"
                     & " in a call to disabled ghost subprogram &",
                     Names => [Root, Subp]),
                  Expr.Expr);

            elsif not Is_Same_Or_Depends_On_Level
                        (Ghost_Assertion_Level (Subp),
                         Ghost_Assertion_Level (Root))
              or else not Is_Same_Or_Depends_On_Level
                            (Ghost_Assertion_Level (Root),
                             Ghost_Assertion_Level (Subp))
            then
               BC_Error
                 (Create
                    ("ghost object & cannot be borrowed"
                     & " in a call to ghost subprogram &",
                     Names => [Root, Subp]),
                  Expr.Expr,
                  Continuations =>
                    [Create
                       ("& and & should have matching assertion levels",
                        Names => [Root, Subp])]);
            end if;
         end;
      end if;

      Check_Expr_Or_Ent (Expr, Mode);
   end Check_Parameter_Or_Global;

   procedure Check_Globals (Subp : Entity_Id; Loc : Node_Id) is
      procedure Check_Global
        (Expr       : Expr_Or_Ent;
         Typ        : Entity_Id;
         Kind       : Formal_Kind;
         Subp       : Entity_Id;
         Global_Var : Boolean);

      procedure Check_Global
        (Expr       : Expr_Or_Ent;
         Typ        : Entity_Id;
         Kind       : Formal_Kind;
         Subp       : Entity_Id;
         Global_Var : Boolean) is
      begin
         Check_Parameter_Or_Global
           (Expr       => Expr,
            Param      => Expr.Ent,
            Typ        => Typ,
            Kind       => Kind,
            Subp       => Subp,
            Global_Var => Global_Var);
      end Check_Global;

      procedure Check_Globals_Inst is new Handle_Globals (Check_Global);

      --  Start of processing for Check_Globals

   begin
      Check_Globals_Inst (Subp, Loc);
   end Check_Globals;

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
            --  Ignored Pragma_Check are not marked. Ignore them.

            if not Is_Ignored_Pragma_Check (Prag) then
               declare
                  Expr : constant Node_Id := Expression (Arg2);
               begin
                  Check_Expression (Expr, Read);
               end;
            end if;

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

         --  These pragmas are re-written and/or removed by the front-end in
         --  GNATprove, so they should never be seen here, unless they are
         --  ignored by virtue of pragma Ignore_Pragma.

         when Pragma_Assert
            | Pragma_Assert_And_Cut
            | Pragma_Assume
            | Pragma_Compile_Time_Error
            | Pragma_Compile_Time_Warning
            | Pragma_Debug
            | Pragma_Loop_Invariant
         =>
            pragma Assert (Should_Ignore_Pragma_Sem (Prag));

         when others =>
            null;
      end case;
   end Check_Pragma;

   ------------------------------------
   -- Check_Simple_Return_Expression --
   ------------------------------------

   procedure Check_Simple_Return_Expression
     (Expr : N_Subexpr_Id; Subp : Entity_Id)
   is
      Return_Typ : constant Entity_Id := Etype (Subp);

   begin
      --  SPARK RM 3.10(6): A return statement that applies to a traversal
      --  function that has an anonymous access-to-constant (respectively,
      --  access-to-variable) result type, shall return either the literal null
      --  or an access object denoted by a direct or indirect observer
      --  (respectively, borrower) of the traversed parameter.
      --
      --  ??? We could possibly allow case and if expressions returning paths
      --  rooted at the right variable. This is done for observers, but not
      --  borrowers. TBD when we know how to support them in proof.
      --  ??? Should we move that to marking? Do we need this check for flow
      --  analysis?

      if Is_Anonymous_Access_Object_Type (Return_Typ) then
         if Nkind (Expr) /= N_Null then
            declare
               Param    : constant Entity_Id := First_Formal (Subp);
               Root     : Entity_Id := Get_Root_Object (Expr);
               Path_Bag : Node_Vectors.Vector;
            begin
               while Root /= Param loop
                  Path_Bag := Get (Current_Observers, Root);
                  if not Path_Bag.Is_Empty then
                     Root := Get_Root_Object (Path_Bag.First_Element);
                  else
                     --  We do not need to look in Current_Borrowers. If the
                     --  ultimate root was Param, then the anonymous access
                     --  object would have been classified as an observer.

                     BC_Error
                       (Create
                          ("return value of a traversal function "
                           & "should be rooted at &",
                           Names => [Param]),
                        Expr);
                     exit;
                  end if;
               end loop;
            end;
         end if;

      --  Otherwise, if the return type is deep, we have a move

      elsif Is_Deep (Return_Typ) then
         pragma Assert (Is_Path_Expression (Expr));

         Check_Expression (Expr, Move);

      elsif Is_Access_Type (Retysp (Return_Typ))
        and then Is_Access_Constant (Retysp (Return_Typ))
        and then Is_Move_To_Constant (Expr)
      then

         --  The expression of the conversion/allocator is moved

         pragma Assert (Is_Path_Expression (Expression (Expr)));
         Check_Expression (Expression (Expr), Move);

      else
         Check_Expression (Expr, Read);
      end if;
   end Check_Simple_Return_Expression;

   ---------------------
   -- Check_Statement --
   ---------------------

   procedure Check_Statement (Stmt : Node_Id) is
   begin
      case N_Statement_Other_Than_Procedure_Call'(Nkind (Stmt)) is

         --  An entry call is handled like other calls

         when N_Entry_Call_Statement =>
            Check_Call_With_Side_Effects (Stmt);

         --  An assignment may correspond to a move, a borrow, or an observe

         when N_Assignment_Statement =>
            declare
               Target : constant Node_Id := Name (Stmt);
               Expr   : constant Node_Id := Expression (Stmt);

            begin
               --  Start with checking that the subexpressions of the target
               --  path are readable, before possibly updating the permission
               --  of these subexpressions in Check_Assignment.

               Check_Expression (Target, Read_Subexpr);

               Check_Assignment (Target => Target, Expr => Expr);

               --  Local observers and borrowers can always be assigned, unless
               --  they are themselves borrowed (for borrowers only). Indeed,
               --  they cannot be moved, and an assignment at top-level is fine
               --  even if the object is observed as it cannot modify the
               --  underlying data structure.

               if Is_Anonymous_Access_Object_Type (Etype (Target)) then
                  pragma
                    Assert (Nkind (Target) in N_Identifier | N_Expanded_Name);

                  declare
                     Root : constant Entity_Id := Entity (Target);
                  begin
                     Check_Not_Borrowed (+Target, Root);

                     --  In the case of reborrow, check that the target object
                     --  is unrestricted (SPARK RM 6.9(7)).

                     if not Is_Access_Constant (Etype (Target)) then
                        declare
                           E_Root    : constant Expr_Or_Ent :=
                             (Is_Ent => True, Ent => Root, Loc => Stmt);
                           Perm_Expl : constant Perm_And_Expl :=
                             Get_Perm_And_Expl (E_Root);
                        begin
                           if Perm_Expl.Perm /= Read_Write then
                              Perm_Error_Reborrow
                                (E          => Root,
                                 N          => Stmt,
                                 Found_Perm => Perm_Expl.Perm,
                                 Expl       => Perm_Expl.Expl);
                           end if;
                        end;
                     end if;
                  end;
               else
                  Check_Expression (Target, Assign);
               end if;
            end;

         when N_Block_Statement =>
            Object_Scope.Push_Scope;
            Check_List (Declarations (Stmt));
            Check_Node (Handled_Statement_Sequence (Stmt));
            Check_End_Of_Scope (Declarations (Stmt));

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
            Object_Scope.Pop_Scope;

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

               Alt := First_Non_Pragma (Alternatives (Stmt));
               Object_Scope.Push_Scope;
               Check_List (Statements (Alt));
               Next_Non_Pragma (Alt);
               Object_Scope.Pop_Scope;

               --  Cleanup

               Move_Env (Current_Perm_Env, New_Env);

               --  Other alternatives

               while Present (Alt) loop

                  --  Restore environment

                  Copy_Env (Saved_Env, Current_Perm_Env);

                  --  Next alternative

                  Object_Scope.Push_Scope;
                  Check_List (Statements (Alt));
                  Next_Non_Pragma (Alt);
                  Object_Scope.Pop_Scope;

                  --  Merge Current_Perm_Env into New_Env

                  Merge_Env (Source => Current_Perm_Env, Target => New_Env);
               end loop;

               Move_Env (New_Env, Current_Perm_Env);
               Free_Env (Saved_Env);
            end;

         when N_Delay_Relative_Statement | N_Delay_Until_Statement =>
            Check_Expression (Expression (Stmt), Read);

         when N_Loop_Statement =>
            Check_Loop_Statement (Stmt);

         when N_Simple_Return_Statement =>
            declare
               Targ : constant Entity_Id :=
                 Return_Applies_To (Return_Statement_Entity (Stmt));
               Expr : constant Node_Id := Expression (Stmt);
            begin
               if Present (Expr) then
                  Check_Simple_Return_Expression (Expr, Targ);
               end if;
               Check_Transfer_Of_Control (Stmt, Unconditional => True);
            end;

         when N_Extended_Return_Statement =>
            Object_Scope.Push_Scope;
            declare
               Subp      : constant Entity_Id :=
                 Return_Applies_To (Return_Statement_Entity (Stmt));
               Decls     : constant List_Id :=
                 Return_Object_Declarations (Stmt);
               Decl      : constant Node_Id := Last_Non_Pragma (Decls);
               Obj       : constant Entity_Id := Defining_Identifier (Decl);
               Perm_Expl : Perm_And_Expl;
            begin
               pragma Assert (not Is_Traversal_Function (Subp));

               Check_List (Return_Object_Declarations (Stmt));
               Check_Node (Handled_Statement_Sequence (Stmt));

               --  Merge environments from inner return

               Merge_Transfer_Of_Control_Env
                 (Current_Extended_Return_Accumulators,
                  Return_Statement_Entity (Stmt));

               declare
                  E_Obj : constant Expr_Or_Ent :=
                    (Is_Ent => True, Ent => Obj, Loc => Decl);
               begin
                  Perm_Expl := Get_Perm_And_Expl (E_Obj);

                  if Perm_Expl.Perm not in Read_Perm then
                     Perm_Error_Subprogram_End
                       (E           => Obj,
                        Subp        => Subp,
                        Found_Perm  => Perm_Expl.Perm,
                        Expl        => Perm_Expl.Expl,
                        Exceptional => False);
                  else
                     Perm_Expl :=
                       Get_Perm_And_Expl (E_Obj, Under_Dereference => True);
                     if Perm_Expl.Perm /= Read_Write then
                        Perm_Error_Subprogram_End
                          (E           => Obj,
                           Subp        => Subp,
                           Found_Perm  => Perm_Expl.Perm,
                           Expl        => Perm_Expl.Expl,
                           Exceptional => False);
                     end if;
                  end if;
               end;

               Check_Transfer_Of_Control (Stmt, Unconditional => True);
            end;
            Object_Scope.Pop_Scope;

         --  On loop exit, merge the current permission environment with the
         --  accumulator for the given loop. The handling for loop
         --  exit/continues is actually the same.

         when N_Exit_Statement | N_Continue_Statement =>
            declare
               Cond     : constant Node_Id := Condition (Stmt);
               Has_Cond : constant Boolean := Present (Cond);
            begin
               if Has_Cond then
                  Check_Expression (Cond, Read);
               end if;
               Check_Transfer_Of_Control (Stmt, Unconditional => not Has_Cond);
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

               Object_Scope.Push_Scope;
               Check_List (Then_Statements (Stmt));
               Object_Scope.Pop_Scope;
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
                     Object_Scope.Push_Scope;
                     Check_List (Then_Statements (Branch));
                     Object_Scope.Pop_Scope;

                     --  Merge current permission environment

                     Merge_Env (Source => Current_Perm_Env, Target => New_Env);
                     Next (Branch);
                  end loop;
               end;

               --  ELSE branch

               --  Restore current permission environment

               Copy_Env (Saved_Env, Current_Perm_Env);
               Object_Scope.Push_Scope;
               Check_List (Else_Statements (Stmt));
               Object_Scope.Pop_Scope;

               --  Merge current permission environment

               Merge_Env (Source => Current_Perm_Env, Target => New_Env);

               --  Cleanup

               Move_Env (New_Env, Current_Perm_Env);
               Free_Env (Saved_Env);
            end;

         when N_Raise_Statement =>

            --  If the exception is handled, merge the environment into the
            --  appropriate handlers accumulators and/or exit the enclosing
            --  procedure.

            Check_Transfer_Of_Control (Stmt, Unconditional => True);

         when N_Null_Statement =>
            null;

         --  When a goto statement is encountered, the current environment is
         --  merged in the appropriate accumulator to be used once the label
         --  is reached. The environment is reset afterward as the path is
         --  cut.

         when N_Goto_Statement =>

            Check_Transfer_Of_Control (Stmt, Unconditional => True);

         --  Unsupported constructs in SPARK

         when N_Abort_Statement
            | N_Accept_Statement
            | N_Asynchronous_Select
            | N_Code_Statement
            | N_Conditional_Entry_Call
            | N_Requeue_Statement
            | N_Selective_Accept
            | N_Timed_Entry_Call
         =>
            null;

         --  Unsupported INOX constructs

         when N_Goto_When_Statement
            | N_Raise_When_Statement
            | N_Return_When_Statement
         =>
            null;

         --  The following nodes are never generated in GNATprove mode

         when N_Compound_Statement | N_Free_Statement =>
            raise Program_Error;
      end case;
   end Check_Statement;

   -------------------------------
   -- Check_Transfer_Of_Control --
   -------------------------------

   procedure Check_Transfer_Of_Control
     (From : Node_Id; Unconditional : Boolean := False)
   is

      Saved_Env : Perm_Env;

      procedure Process (Scop : Node_Id);
      --  Deal with scope exit:
      --  * When escaping declaration scopes, check that borrowers are left
      --    in unrestricted state
      --  * When crossing through a finally, check the finally statements with
      --    current environment

      procedure Stop
        (Destination : Node_Id;
         Exc_Set     : Exception_Sets.Set;
         Is_Continue : Boolean);
      --  Deal with accumulating permission environment at destination of
      --  transfer of control. For transfer of control escaping the subprogram,
      --  check permission environments are in the expected state.

      procedure Main_Iteration is new
        Iter_Exited_Scopes (Process, Stop => Stop);

      -------------
      -- Process --
      -------------

      procedure Process (Scop : Node_Id) is
      begin
         case Nkind (Scop) is
            --  For exited blocks/bodies, check that declared borrowers are
            --  in the unrestricted state.

            when N_Block_Statement =>
               Check_End_Of_Scope (Declarations (Scop), N => From);

            when N_Entity =>
               Check_End_Of_Scope (Declarations (Get_Body (Scop)), N => From);

            --  For exiting paths through finally statements, carry the
            --  permission environment through the finally section.

            when N_Handled_Sequence_Of_Statements =>
               if Present (Finally_Statements (Scop)) then
                  Object_Scope.Push_Scope;
                  Check_List (Finally_Statements (Scop));
                  Object_Scope.Pop_Scope;
               end if;

            --  No ownership is supported in for loop cursor/objects right now,
            --  and extended_return cannot declare borrowers nor observers, so
            --  nothing needs to be done for these cases.

            when N_Loop_Statement
               | N_Iteration_Scheme
               | N_Extended_Return_Statement
            =>
               null;

            when others =>
               raise Program_Error;
         end case;
      end Process;

      ----------
      -- Stop --
      ----------

      procedure Stop
        (Destination : Node_Id;
         Exc_Set     : Exception_Sets.Set;
         Is_Continue : Boolean)
      is
         procedure Do_Local (Env_Map : in out Env_Backups; Key : Node_Id);
         --  Common processing for transfer-of-control stopping within current
         --  body. The corresponding map and keys should be passed as
         --  parameter.

         --------------
         -- Do_Local --
         --------------

         procedure Do_Local (Env_Map : in out Env_Backups; Key : Node_Id) is
            Saved_Accumulator : constant Perm_Env_Access := Get (Env_Map, Key);
            Environment_Copy  : constant Perm_Env_Access := new Perm_Env;
         begin
            Copy_Env (Current_Perm_Env, Environment_Copy.all);

            if Saved_Accumulator = null then
               Set (Env_Map, Key, Environment_Copy);
            else
               Merge_Env
                 (Source => Environment_Copy.all,
                  Target => Saved_Accumulator.all);
            end if;
         end Do_Local;

         --  Start of processing for Stop

      begin
         case Nkind (Destination) is
            when N_Loop_Statement =>
               declare
                  Loop_Name : constant Entity_Id :=
                    Entity (Identifier (Destination));
               begin
                  if Is_Continue then
                     Do_Local (Current_Continue_Accumulators, Loop_Name);
                  else
                     Do_Local (Current_Exit_Accumulators, Loop_Name);
                  end if;
               end;

            when N_Exception_Handler =>

               Do_Local (Current_Exc_Accumulators, Destination);

            when N_Extended_Return_Statement =>

               Do_Local
                 (Current_Extended_Return_Accumulators,
                  Return_Statement_Entity (Destination));

            when N_Entity =>
               if Ekind (Destination) = E_Label then
                  Do_Local (Current_Goto_Accumulators, Destination);
               else
                  declare
                     Subp : Entity_Id renames Destination;
                  begin
                     pragma Assert (Ekind (Subp) in Subprogram_Kind | E_Entry);

                     --  Check out parameters and globals at exit

                     if Ekind (Subp) in E_Procedure | E_Entry
                       or else (Ekind (Subp) = E_Function
                                and then Is_Function_With_Side_Effects (Subp))
                     then
                        Return_Parameters
                          (Subp, Exceptional => not Exc_Set.Is_Empty);
                     end if;
                     Return_Globals
                       (Subp, Exceptional => not Exc_Set.Is_Empty);

                     --  For operations directly inside protected objects,
                     --  check the permission of protected components on
                     --  return.

                     if Ekind (Scope (Subp)) = E_Protected_Type
                       and then (Is_Entry (Subp)
                                 or else Ekind (Subp) = E_Procedure)
                     then
                        Return_Protected_Components (Subp);
                     end if;
                  end;
               end if;

            when others =>
               raise Program_Error;
         end case;
      end Stop;

   begin
      --  Save current permission environment. Not needed for unconditional
      --  jumps as we reset the environment afterward anyway.

      if not Unconditional then
         Copy_Env (Current_Perm_Env, Saved_Env);
      end if;
      Main_Iteration (From);
      if Unconditional then
         Reset_Env (Current_Perm_Env);
      else
         Move_Env (Saved_Env, Current_Perm_Env);
      end if;
   end Check_Transfer_Of_Control;

   ----------------------------
   -- Found_Permission_Error --
   ----------------------------

   function Found_Permission_Error return Boolean
   is (Permission_Error);

   -----------------------
   -- Get_Perm_And_Expl --
   -----------------------

   function Get_Perm_And_Expl
     (N : Expr_Or_Ent; Under_Dereference : Boolean := False)
      return Perm_And_Expl
   is
      --  Local subprograms

      function Glb_Expl (P1, P2 : Perm_And_Expl) return Perm_And_Expl;
      --  Generalize Glb to permission with explanations. Currently,
      --  non-trivial join should be impossible, so there should always be a
      --  coherent explanation.

      function Scan_Under_Dereference
        (T : Perm_Tree_Access) return Perm_And_Expl;
      --  Return greatest lower bound of permissions reachable under
      --  dereferences of parts abstracted by T, together with a suitable
      --  explanation.

      --------------
      -- Glb_Expl --
      --------------

      function Glb_Expl (P1, P2 : Perm_And_Expl) return Perm_And_Expl is
      begin
         return
            Res : Perm_And_Expl :=
              (Perm => Glb (P1.Perm, P2.Perm), Expl => P1.Expl)
         do
            --  If P2 provides a suitable explanation and P1 does not, take
            --  that of P2 instead.

            if P2.Perm = Res.Perm
              and then (No (Res.Expl) or else P1.Perm /= Res.Perm)
            then
               Res.Expl := P2.Expl;

            --  If neither P1 nor P2 provides a suitable explanation, this
            --  means we are making the greatest lower bound of a read-only and
            --  a write-only permission. Currently, that case is not possible.

            elsif P1.Perm /= Res.Perm and then P2.Perm /= Res.Perm then
               raise Program_Error;
            end if;
         end return;
      end Glb_Expl;

      ----------------------------
      -- Scan_Under_Dereference --
      ----------------------------

      function Scan_Under_Dereference
        (T : Perm_Tree_Access) return Perm_And_Expl is
      begin
         --  If T is not deep, no part can be reached under a dereference, so
         --  they are all read/write. No suitable explanation can be provided,
         --  but none is needed, the subsequent test can never fail with
         --  maximum permission.

         if not Is_Node_Deep (T) then
            return (Perm => Read_Write, Expl => Types.Empty);
         end if;
         case Kind (T) is
            when Entire_Object =>
               return
                 (Perm => Children_Permission (T), Expl => Explanation (T));

            when Reference =>
               return
                 (Perm => Permission (Get_All (T)),
                  Expl => Explanation (Get_All (T)));

            when Array_Component =>
               return Scan_Under_Dereference (Get_Elem (T));

            when Record_Component =>
               return
                  Result : Perm_And_Expl :=
                    (Perm => Read_Write, Expl => Types.Empty)
               do
                  declare
                     Comp : constant Perm_Tree_Maps.Instance := Component (T);
                     Key  : Perm_Tree_Maps.Key_Option :=
                       Perm_Tree_Maps.Get_First_Key (Comp);
                  begin
                     while Key.Present loop
                        Result :=
                          Glb_Expl
                            (Result,
                             Scan_Under_Dereference
                               (Perm_Tree_Maps.Get (Comp, Key.K)));
                        Key := Perm_Tree_Maps.Get_Next_Key (Comp);
                     end loop;
                  end;
               end return;
         end case;
      end Scan_Under_Dereference;

      --  Local variables

      Do_Under_Dereference : Boolean := Under_Dereference;
      Limit_To_Read_Only   : Boolean := False;
      Main_Path            : Node_Id :=
        (if not N.Is_Ent then N.Expr else N.Ent);
      Result               : Perm_And_Expl;

      --  Start of processing for Get_Perm_And_Expl

   begin
      --  If the expression contains a toplevel 'Access, resulting permissions
      --  may be affected.
      --  * The result of an 'Access operation is not a view of a part of
      --    N.Expr anymore. It can never be written. In effect, this limits the
      --    maximum possible permission to Read_Only.
      --  * If we want the permission for parts reachable under dereference,
      --    the effect of 'Access and the Under_Dereference flag cancel out
      --    instead.

      if not N.Is_Ent
        and then N.Expr in N_Attribute_Reference_Id
        and then Get_Attribute_Id (Attribute_Name (N.Expr)) = Attribute_Access
      then
         Main_Path := Prefix (N.Expr);
         if Do_Under_Dereference then
            Do_Under_Dereference := False;
         else
            Limit_To_Read_Only := True;
         end if;
      end if;

      --  The expression has a shallow type, and we want parts that can be
      --  reached under dereference. Since there are none, we give Read_Write
      --  permission. We need to single out this case early because the tree
      --  might be folded on a prefix.

      if Do_Under_Dereference and then not Is_Deep (Retysp (Etype (Main_Path)))
      then
         Result := (Perm => Read_Write, Expl => Types.Empty);

      --  The expression is directly rooted in an object

      elsif N.Is_Ent
        or else Present
                  (Get_Root_Object (Main_Path, Through_Traversal => False))
      then
         declare
            Tree_Or_Perm : constant Perm_Or_Tree :=
              Get_Perm_Or_Tree
                (if N.Is_Ent then N else (Is_Ent => False, Expr => Main_Path));
         begin
            case Tree_Or_Perm.R is
               when Folded =>
                  Result :=
                    (Perm => Tree_Or_Perm.Found_Permission,
                     Expl => Tree_Or_Perm.Explanation);

               when Unfolded =>
                  declare
                     Tree_Ptr : constant Perm_Tree_Access :=
                       Tree_Or_Perm.Tree_Access;
                  begin
                     pragma Assert (Tree_Ptr /= null);

                     if Do_Under_Dereference then
                        Result := Scan_Under_Dereference (Tree_Ptr);
                     else
                        Result :=
                          (Perm => Permission (Tree_Ptr),
                           Expl => Explanation (Tree_Ptr));
                     end if;
                  end;
            end case;
         end;
      else
         declare
            Root : constant Node_Id :=
              Get_Root_Expr (Main_Path, Through_Traversal => False);
         begin

            --  The expression is rooted in a call to a traversal function. The
            --  type of the result determine the permissions of everything that
            --  is accessible from it.

            if Is_Traversal_Function_Call (Root) then
               Result :=
                 (Perm =>
                    (if Is_Access_Constant (Etype (Get_Called_Entity (Root)))
                     then Read_Only
                     else Read_Write),
                  Expl => Main_Path);

            --  The expression is a function call, an allocation, or null. The
            --  result is freshly allocated, everything in it can be read and
            --  written.

            else
               Result := (Perm => Read_Write, Expl => Main_Path);
            end if;
         end;
      end if;

      --  Limit permission to Read_Only if needed

      if Limit_To_Read_Only
        and then Result.Perm in Read_Perm
        and then Result.Perm /= Read_Only
      then
         Result.Perm := Read_Only;
         Result.Expl := N.Expr;
      end if;

      return Result;
   end Get_Perm_And_Expl;

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
           Query_Read_Only_Tree (Current_Perm_Env, Unique_Entity_In_SPARK (E));
      begin
         --  The root object should have been declared and entered into the
         --  current permission environment.

         if C = null then

            --  If E is a variable and it is not in the environment, it must
            --  be missing from the global contract of the enclosing
            --  subprogram. Raise an error.

            if Ekind (E) /= E_Constant
              or else Is_Access_Variable (Etype (E))
              or else Has_Variable_Input (E)
            then
               pragma Assert (Present (Current_Subp));
               BC_Error
                 (Create
                    ("owning or observing object should occur in the global"
                     & " contract of &",
                     Names => [Current_Subp]),
                  E);
            end if;

            --  If E is a constant without variable inputs, it has permission
            --  Read_Only.

            return
              (R => Folded, Found_Permission => Read_Only, Explanation => E);
         end if;

         return (R => Unfolded, Tree_Access => C);
      end Get_Perm_Or_Tree_Ent;

   begin
      if N.Is_Ent then
         return Get_Perm_Or_Tree_Ent (N.Ent);
      end if;

      case Nkind (N.Expr) is

         when N_Expanded_Name | N_Identifier =>
            return Get_Perm_Or_Tree_Ent (Entity (N.Expr));

         --  For a nonterminal path, we get the permission tree of its
         --  prefix, and then get the subtree associated with the extension,
         --  if unfolded. If folded, we return the permission associated with
         --  children.

         when N_Explicit_Dereference
            | N_Indexed_Component
            | N_Selected_Component
            | N_Slice
            | N_Attribute_Reference
            | N_Op_Ne
            | N_Op_Eq
         =>
            pragma
              Assert
                (if Nkind (N.Expr) = N_Attribute_Reference
                   then
                     Get_Attribute_Id (Attribute_Name (N.Expr))
                     in Attribute_First | Attribute_Last | Attribute_Length);

            declare
               Pref : constant Node_Id :=
                 (if Nkind (N.Expr) not in N_Op_Eq | N_Op_Ne
                  then Prefix (N.Expr)
                  elsif Nkind (Left_Opnd (N.Expr)) = N_Null
                  then Right_Opnd (N.Expr)
                  else Left_Opnd (N.Expr));
               C    : constant Perm_Or_Tree := Get_Perm_Or_Tree (+Pref);
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
                           return
                             (R                => Folded,
                              Found_Permission =>
                                Children_Permission (C.Tree_Access),
                              Explanation      => Explanation (C.Tree_Access));

                        when Reference =>
                           pragma
                             Assert
                               (Nkind (N.Expr)
                                in N_Explicit_Dereference | N_Op_Ne | N_Op_Eq);

                           if Nkind (N.Expr) = N_Explicit_Dereference then
                              return
                                (R           => Unfolded,
                                 Tree_Access => Get_All (C.Tree_Access));
                           else
                              return
                                (R                => Folded,
                                 Found_Permission =>
                                   Null_Permission (C.Tree_Access),
                                 Explanation      =>
                                   Explanation (C.Tree_Access));
                           end if;

                        when Record_Component =>
                           pragma
                             Assert (Nkind (N.Expr) = N_Selected_Component);
                           declare
                              Comp : constant Entity_Id :=
                                Original_Record_Component
                                  (Entity (Selector_Name (N.Expr)));
                              D    : constant Perm_Tree_Access :=
                                Perm_Tree_Maps.Get
                                  (Component (C.Tree_Access), Comp);
                           begin
                              pragma Assert (D /= null);
                              return (R => Unfolded, Tree_Access => D);
                           end;

                        when Array_Component =>
                           pragma
                             Assert
                               (Nkind (N.Expr) = N_Indexed_Component
                                  or else Nkind (N.Expr) = N_Slice
                                  or else Nkind (N.Expr)
                                          = N_Attribute_Reference);

                           if Nkind (N.Expr) = N_Attribute_Reference then
                              pragma
                                Assert
                                  (Attribute_Name (N.Expr)
                                   in Name_Last | Name_First | Name_Length);
                              return
                                (R                => Folded,
                                 Found_Permission =>
                                   Bounds_Permission (C.Tree_Access),
                                 Explanation      =>
                                   Explanation (C.Tree_Access));
                           elsif Nkind (N.Expr) = N_Slice then
                              return C;
                           else
                              pragma Assert (Get_Elem (C.Tree_Access) /= null);
                              return
                                (R           => Unfolded,
                                 Tree_Access => Get_Elem (C.Tree_Access));
                           end if;
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

   function Glb (P1, P2 : Perm_Kind) return Perm_Kind is
   begin
      case P1 is
         when No_Access =>
            return No_Access;

         when Read_Only =>
            case P2 is
               when No_Access | Write_Only =>
                  return No_Access;

               when Read_Perm =>
                  return Read_Only;
            end case;

         when Write_Only =>
            case P2 is
               when No_Access | Read_Only =>
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
         when N_Expanded_Name | N_Identifier =>
            return False;

         when N_Explicit_Dereference | N_Selected_Component =>
            return Has_Array_Component (Prefix (Expr));

         when N_Indexed_Component | N_Slice =>
            return True;

         when N_Allocator | N_Null | N_Function_Call =>
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

   pragma
     Annotate
       (Xcov,
        Exempt_On,
        "Only used in the debugger to look into a hash table");
   procedure Hp (P : Perm_Env) is
      Elem : Perm_Tree_Maps.Key_Option;

   begin
      Elem := Get_First_Key (P);
      while Elem.Present loop
         Print_Node_Briefly (Elem.K);
         Elem := Get_Next_Key (P);
      end loop;
   end Hp;
   pragma Annotate (Xcov, Exempt_Off);

   -------------------------
   -- Is_Move_To_Constant --
   -------------------------

   function Is_Move_To_Constant (Expr : Node_Id) return Boolean is
   begin
      case Nkind (Expr) is

         --  The initial value of the an access-to-constant allocator is
         --  moved if the designated type is deep.

         when N_Allocator =>
            --  Ada RM 4.8(5/2): If the type of the allocator is an
            --  access-to-constant type, the allocator shall be an
            --  initialized allocator.
            pragma Assert (Nkind (Expression (Expr)) = N_Qualified_Expression);
            declare
               Des_Ty : Entity_Id :=
                 Directly_Designated_Type (Retysp (Etype (Expr)));
            begin
               if Is_Incomplete_Type (Des_Ty)
                 and then Present (Full_View (Des_Ty))
               then
                  Des_Ty := Full_View (Des_Ty);
               end if;

               return
                 Is_Deep (Des_Ty)
                 and then not Is_Rooted_In_Constant (Expression (Expr));
            end;

         --  A conversion from an access-to-variable type to an
         --  access-to-constant type is a move.

         when N_Type_Conversion | N_Unchecked_Type_Conversion =>
            return
              not (Is_Access_Constant (Retysp (Etype (Expression (Expr))))
                   or else Is_Rooted_In_Constant (Expression (Expr)));

         when others =>
            return False;
      end case;
   end Is_Move_To_Constant;

   -------------------------
   -- Is_Prefix_Or_Almost --
   -------------------------

   function Is_Prefix_Or_Almost
     (Pref : Node_Id; Expr : Expr_Or_Ent) return Boolean
   is

      type Expr_Array is array (Positive range <>) of Node_Or_Entity_Id;
      --  Sequence of expressions that make up a path. The first element is
      --  always an entity when the path has a root.

      function Get_Expr_Array (Expr : Node_Id) return Expr_Array;
      pragma Precondition (Is_Path_Expression (Expr));
      --  Return the sequence of expressions that make up a path, excluding
      --  slices.

      --------------------
      -- Get_Expr_Array --
      --------------------

      function Get_Expr_Array (Expr : Node_Id) return Expr_Array is
      begin
         case Nkind (Expr) is
            when N_Expanded_Name | N_Identifier =>
               return Expr_Array'(1 => Entity (Expr));

            when N_Slice =>
               return Get_Expr_Array (Prefix (Expr));

            when N_Explicit_Dereference
               | N_Indexed_Component
               | N_Selected_Component
               | N_Attribute_Reference
            =>
               return Get_Expr_Array (Prefix (Expr)) & Expr;

            when N_Qualified_Expression
               | N_Type_Conversion
               | N_Unchecked_Type_Conversion
            =>
               return Get_Expr_Array (Expression (Expr));

            when N_Op_Ne | N_Op_Eq =>
               if Nkind (Left_Opnd (Expr)) = N_Null then
                  return Get_Expr_Array (Right_Opnd (Expr)) & Expr;
               else
                  pragma Assert (Nkind (Right_Opnd (Expr)) = N_Null);
                  return Get_Expr_Array (Left_Opnd (Expr)) & Expr;
               end if;

            when others =>
               raise Program_Error;
         end case;
      end Get_Expr_Array;

      --  Local variables

      Prefix_Path : constant Expr_Array := Get_Expr_Array (Pref);
      Expr_Path   : constant Expr_Array :=
        (if Expr.Is_Ent
         then (1 => Expr.Ent)
         else Get_Expr_Array (Get_Observed_Or_Borrowed_Expr (Expr.Expr)));

      Prefix_Root : constant Entity_Id := Prefix_Path (1);
      Expr_Root   : constant Entity_Id := Expr_Path (1);

      Common_Len : constant Positive :=
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

            if Nkind (Prefix_Elt) /= Nkind (Expr_Elt) then
               return False;
            end if;

            case Nkind (Prefix_Elt) is
               when N_Explicit_Dereference | N_Indexed_Component =>
                  null;

               when N_Op_Ne | N_Op_Eq | N_Attribute_Reference =>
                  --  Prefix and Expr cannot be equality operators together,
                  --  nor attribute references together, as one or the other
                  --  necessarily is a borrowed expression.

                  raise Program_Error;

               when N_Selected_Component =>
                  if Original_Record_Component
                       (Entity (Selector_Name (Prefix_Elt)))
                    /= Original_Record_Component
                         (Entity (Selector_Name (Expr_Elt)))
                  then
                     return False;
                  end if;

               when others =>
                  raise Program_Error;
            end case;
         end;
      end loop;

      --  If the expression path is longer than the prefix one, then at this
      --  point the prefix property holds.

      if Expr_Path'Length >= Prefix_Path'Length then
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
   begin
      if Ekind (E) = E_Variable then
         declare
            Typ : constant Entity_Id := Etype (E);
         begin
            if Is_Anonymous_Access_Object_Type (Typ)
              and then Is_Access_Constant (Typ)
            then
               --  Strictly speaking, observers can be written. However, this
               --  is irrelevant for the borrow-checker as we check such
               --  assignments (re-observe) in a special way. The permission
               --  for designated value is the relevant bit, and they are
               --  read-only.

               return True;
            end if;
         end;
      end if;

      --  Other cases are covered by Is_Constant_In_SPARK

      return Is_Constant_In_SPARK (E);

   end Is_Read_Only;

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
               when No_Access | Read_Only =>
                  return Read_Only;

               when Write_Perm =>
                  return Read_Write;
            end case;

         when Write_Only =>
            case P2 is
               when No_Access | Write_Only =>
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

   procedure Merge_Env
     (Source : in out Perm_Env;
      Target : in out Perm_Env;
      Filter : Boolean := False)
   is

      --  Local subprograms

      procedure Apply_Glb_Tree (A : Perm_Tree_Access; P : Perm_Kind);

      procedure Merge_Trees
        (Target : Perm_Tree_Access; Source : Perm_Tree_Access);

      --------------------
      -- Apply_Glb_Tree --
      --------------------

      procedure Apply_Glb_Tree (A : Perm_Tree_Access; P : Perm_Kind) is
      begin
         A.all.Tree.Permission := Glb (Permission (A), P);

         case Kind (A) is
            when Entire_Object =>
               A.all.Tree.Children_Permission :=
                 Glb (Children_Permission (A), P);

            when Reference =>
               Apply_Glb_Tree (Get_All (A), P);
               A.all.Tree.Null_Permission := Glb (Null_Permission (A), P);

            when Array_Component =>
               Apply_Glb_Tree (Get_Elem (A), P);
               A.all.Tree.Bounds_Permission := Glb (Bounds_Permission (A), P);

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
        (Target : Perm_Tree_Access; Source : Perm_Tree_Access)
      is
         Perm : constant Perm_Kind :=
           Glb (Permission (Target), Permission (Source));

      begin
         --  If permission of Target is about to change, then use the
         --  explanation from Source as the reason for the reduced permission.
         if Perm /= Permission (Target) then
            Target.all.Tree.Explanation := Explanation (Source);
         end if;

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
                        Target.all.Tree.Null_Permission :=
                          Glb (Child_Perm, Null_Permission (Source));
                        Target.all.Tree.Permission := Perm;
                        Apply_Glb_Tree (Get_All (Target), Child_Perm);

                     when Array_Component =>
                        Copy_Tree (Source, Target);
                        Target.all.Tree.Bounds_Permission :=
                          Glb (Child_Perm, Bounds_Permission (Source));
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
                              Comp :=
                                Perm_Tree_Maps.Get_Next (Component (Target));
                           end loop;
                        end;
                  end case;
               end;

            when Reference =>
               case Kind (Source) is
                  when Entire_Object =>
                     Target.all.Tree.Null_Permission :=
                       Glb
                         (Null_Permission (Target),
                          Children_Permission (Source));
                     Apply_Glb_Tree
                       (Get_All (Target), Children_Permission (Source));

                  when Reference =>
                     Target.all.Tree.Null_Permission :=
                       Glb
                         (Null_Permission (Target), Null_Permission (Source));
                     Merge_Trees (Get_All (Target), Get_All (Source));

                  when others =>
                     raise Program_Error;

               end case;

            when Array_Component =>
               case Kind (Source) is
                  when Entire_Object =>
                     Target.all.Tree.Bounds_Permission :=
                       Glb
                         (Bounds_Permission (Target),
                          Children_Permission (Source));
                     Apply_Glb_Tree
                       (Get_Elem (Target), Children_Permission (Source));

                  when Array_Component =>
                     Target.all.Tree.Bounds_Permission :=
                       Glb
                         (Bounds_Permission (Target),
                          Bounds_Permission (Source));
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
                        Comp := Perm_Tree_Maps.Get_First (Component (Target));
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
                        Key_Source :=
                          Perm_Tree_Maps.Get_First_Key (Component (Source));

                        while Key_Source.Present loop
                           CompSource :=
                             Perm_Tree_Maps.Get
                               (Component (Source), Key_Source.K);
                           CompTarget :=
                             Perm_Tree_Maps.Get
                               (Component (Target), Key_Source.K);

                           pragma Assert (CompSource /= null);
                           Merge_Trees (CompTarget, CompSource);

                           Key_Source :=
                             Perm_Tree_Maps.Get_Next_Key (Component (Source));
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
      KeyTarget  : Perm_Tree_Maps.Key_Option;

      --  Start of processing for Merge_Env

   begin
      KeyTarget := Get_First_Key (Target);

      --  Iterate over every tree of the environment in the target, and merge
      --  it with the source if there is such a similar one that exists. If
      --  there is none, then skip.

      while KeyTarget.Present loop

         CompSource := Query_Mutable_Tree (Source, KeyTarget.K);
         CompTarget := Query_Mutable_Tree (Target, KeyTarget.K);

         pragma Assert (CompTarget /= null);

         if CompSource /= null then
            if not (Filter and then Get (Default_Perm_Env, KeyTarget.K) = null)
            then
               Merge_Trees (CompTarget, CompSource);
            end if;
            Remove (Source, KeyTarget.K);
            Free_Tree (CompSource);
         end if;

         KeyTarget := Get_Next_Key (Target);
      end loop;

      --  Transfer remaining trees from source to target, merging if necessary.
      --  There may be corresponding trees from target because of the default
      --  environment.

      declare
         KeySource : Perm_Tree_Maps.Key_Option;
      begin
         KeySource := Get_First_Key (Source);
         while KeySource.Present loop

            CompSource := Query_Mutable_Tree (Source, KeySource.K);
            CompTarget := Query_Mutable_Tree (Target, KeySource.K);

            pragma Assert (CompSource /= null);

            Remove (Source, KeySource.K);

            if Filter and then Get (Default_Perm_Env, KeySource.K) = null then
               Free_Tree (CompSource);
            elsif CompTarget /= null then
               Merge_Trees (CompTarget, CompSource);
               Remove (Source, KeySource.K);
               Free_Tree (CompSource);
            else
               Set (Target, KeySource.K, CompSource);
               Remove (Source, KeySource.K);
            end if;

            KeySource := Get_First_Key (Source);
         end loop;
      end;
   end Merge_Env;

   -----------------------------------
   -- Merge_Transfer_Of_Control_Env --
   -----------------------------------

   procedure Merge_Transfer_Of_Control_Env
     (Map : in out Env_Backups; Key : Node_Id)
   is
      Saved_Env : constant Perm_Env_Access := Get (Map, Key);
   begin
      if Saved_Env /= null then
         Merge_Env (Saved_Env.all, Current_Perm_Env, Filter => True);
         Remove (Map, Key);
      end if;
   end Merge_Transfer_Of_Control_Env;

   ------------------
   -- Object_Scope --
   ------------------

   package body Object_Scope is

      package Index_Vectors is new
        Ada.Containers.Vectors
          (Index_Type   => Positive,
           Element_Type => Node_Vectors.Extended_Index);

      Object_Stack : Node_Vectors.Vector;
      --  Stack of objects declared in the current scope

      Scoping_Stack : Index_Vectors.Vector;
      --  Stack to keep the implicit sector delimitation. The stack stores the
      --  last index of sectors before the current 'open' sector (the one that
      --  can be extended by Push_Object).

      ----------------------
      -- Is_Initial_Value --
      ----------------------

      function Is_Initial_Value return Boolean
      is (Object_Stack.Is_Empty and then Scoping_Stack.Is_Empty);

      ---------------
      -- Pop_Scope --
      ---------------

      procedure Pop_Scope is
         pragma Assert (not Scoping_Stack.Is_Empty);
         Index : Node_Vectors.Extended_Index := Object_Stack.Last_Index;
         Limit : constant Node_Vectors.Extended_Index :=
           Scoping_Stack.Last_Element;
         Total : constant Count_Type := Count_Type (Index - Limit);
      begin
         while Index /= Limit loop
            declare
               E : constant Entity_Id := Object_Stack.Element (Index);
            begin
               Remove (Default_Perm_Env, E);
               Remove (Current_Perm_Env, E);
            end;
            Index := Index - 1;
         end loop;
         Object_Stack.Delete_Last (Count => Total);
         Scoping_Stack.Delete_Last;
      end Pop_Scope;

      -----------------
      -- Push_Object --
      -----------------

      procedure Push_Object (E : Entity_Id) is
      begin
         Object_Stack.Append (E);
      end Push_Object;

      ----------------
      -- Push_Scope --
      ----------------

      procedure Push_Scope is
      begin
         Scoping_Stack.Append (Object_Stack.Last_Index);
      end Push_Scope;

   end Object_Scope;

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
         Part  : out Boolean;
         Deref : out Boolean);
      --  Set the root object Obj, and whether the path contains a part and a
      --  dereference, from a path Path.

      ---------------------
      -- Set_Root_Object --
      ---------------------

      procedure Set_Root_Object
        (Path  : Node_Id;
         Obj   : out Entity_Id;
         Part  : out Boolean;
         Deref : out Boolean) is
      begin
         case Nkind (Path) is
            when N_Identifier | N_Expanded_Name =>
               Obj := Entity (Path);
               Part := False;
               Deref := False;

            when N_Type_Conversion
               | N_Unchecked_Type_Conversion
               | N_Qualified_Expression
            =>
               Set_Root_Object (Expression (Path), Obj, Part, Deref);

            when N_Indexed_Component
               | N_Selected_Component
               | N_Slice
               | N_Attribute_Reference
            =>
               Set_Root_Object (Prefix (Path), Obj, Part, Deref);
               Part := True;

            when N_Explicit_Dereference =>
               Set_Root_Object (Prefix (Path), Obj, Part, Deref);
               Deref := True;

            when N_Op_Ne | N_Op_Eq =>
               if Nkind (Left_Opnd (Path)) = N_Null then
                  Set_Root_Object (Right_Opnd (Path), Obj, Part, Deref);
               else
                  pragma Assert (Nkind (Right_Opnd (Path)) = N_Null);
                  Set_Root_Object (Left_Opnd (Path), Obj, Part, Deref);
               end if;
               Part := True;

            when others =>
               raise Program_Error;
         end case;
      end Set_Root_Object;

      --  Local variables

      Root           : Entity_Id;
      Part, Is_Deref : Boolean;

      Loc : constant Node_Id := (if N.Is_Ent then N.Loc else N.Expr);

      --  Start of processing for Perm_Error

   begin
      if N.Is_Ent then
         Part := False;
         Is_Deref := False;
         Root := N.Ent;
      else
         Set_Root_Object (N.Expr, Root, Part, Is_Deref);
      end if;

      BC_Error
        (Create
           ((if Part then "part of " else "")
            & (if Is_Deref then "dereference from " else "")
            & "& is not "
            & (if (Perm in Read_Perm and then Found_Perm not in Read_Perm)
                 or else Forbidden_Perm
               then "readable"
               else "writable"),
            Names => [Root]),
         Loc,
         Continuations =>
           [Perm_Mismatch (N, Perm, Found_Perm, Expl, Forbidden_Perm)]);
   end Perm_Error;

   ---------------------------
   -- Perm_Error_Borrow_End --
   ---------------------------

   procedure Perm_Error_Borrow_End
     (E : Entity_Id; N : Node_Id; Found_Perm : Perm_Kind; Expl : Node_Id)
   is
      Ent : constant Expr_Or_Ent := (Is_Ent => True, Ent => E, Loc => E);
   begin
      BC_Error
        (Create ("borrower & exits its scope with moved value", Names => [E]),
         N,
         Continuations => [Perm_Mismatch (Ent, Read_Write, Found_Perm, Expl)]);
   end Perm_Error_Borrow_End;

   -------------------------------
   -- Perm_Error_Subprogram_End --
   -------------------------------

   procedure Perm_Error_Subprogram_End
     (E           : Entity_Id;
      Subp        : Entity_Id;
      Found_Perm  : Perm_Kind;
      Expl        : Node_Id;
      Exceptional : Boolean)
   is
      Ent        : constant Expr_Or_Ent :=
        (Is_Ent => True, Ent => E, Loc => Subp);
      Conts      : constant Message_Lists.List :=
        [Perm_Mismatch (Ent, Read_Write, Found_Perm, Expl)];
      Msg_String : constant String :=
        (if Exceptional
         then "exceptional exit from & with moved value for &"
         else "return from & with moved value for &");
   begin
      BC_Error
        (Create (Msg_String, Names => [Subp, E]),
         Subp,
         Continuations => Conts);
   end Perm_Error_Subprogram_End;

   -------------------------
   -- Perm_Error_Reborrow --
   -------------------------

   procedure Perm_Error_Reborrow
     (E : Entity_Id; N : Node_Id; Found_Perm : Perm_Kind; Expl : Node_Id)
   is
      Ent : constant Expr_Or_Ent := (Is_Ent => True, Ent => E, Loc => E);
   begin
      BC_Error
        (Create ("borrower & is reborrowed with moved value", Names => [E]),
         N,
         Continuations => [Perm_Mismatch (Ent, Read_Write, Found_Perm, Expl)]);
   end Perm_Error_Reborrow;

   -------------------
   -- Perm_Mismatch --
   -------------------

   function Perm_Mismatch
     (N              : Expr_Or_Ent;
      Exp_Perm       : Perm_Kind;
      Act_Perm       : Perm_Kind;
      Expl           : Node_Id;
      Forbidden_Perm : Boolean := False) return Message
   is
      Borrowed : constant Node_Id := Check_On_Borrowed (N);
      Observed : constant Node_Id := Check_On_Observed (N);
      Reason   : constant String :=
        (if Present (Observed)
         then "observed #"
         elsif Present (Borrowed)
         then "borrowed #"
         else "moved #");
      Code     : constant Explain_Code_Kind :=
        (if Present (Observed) or else Present (Borrowed)
         then EC_None
         else EC_Ownership_Moved_Object);
      Sec_Sloc : constant Source_Ptr := Sloc (Expl);
   begin
      if Forbidden_Perm then
         if Exp_Perm = No_Access then
            return
              Create
                ("object was " & Reason,
                 Explain_Code  => Code,
                 Secondary_Loc => Sec_Sloc);
         else
            raise Program_Error;
         end if;
      else
         case Exp_Perm is
            when Write_Perm =>
               if Act_Perm = Read_Only then
                  return
                    Create
                      ("object was declared as not writable #",
                       Secondary_Loc => Sec_Sloc);
               else
                  return
                    Create
                      ("object was " & Reason,
                       Explain_Code  => Code,
                       Secondary_Loc => Sec_Sloc);
               end if;

            when Read_Only =>
               return
                 Create
                   ("object was " & Reason,
                    Explain_Code  => Code,
                    Secondary_Loc => Sec_Sloc);

            when No_Access =>
               raise Program_Error;
         end case;
      end if;
   end Perm_Mismatch;

   ------------------
   -- Process_Path --
   ------------------

   procedure Process_Path (Expr : Expr_Or_Ent; Mode : Checking_Mode) is
      Expr_Type : constant Entity_Id :=
        (if Expr.Is_Ent then Etype (Expr.Ent) else Etype (Expr.Expr));
      Root      : Entity_Id :=
        (if Expr.Is_Ent then Expr.Ent else Get_Root_Object (Expr.Expr));
      Loc       : constant Node_Id :=
        (if Expr.Is_Ent then Expr.Loc else Expr.Expr);
      Perm      : Perm_Kind_Option;
      Expl      : Node_Id;

   begin
      --  Nothing to do if the path is not rooted in an object

      if No (Root) or else not Is_Object (Root) then
         return;
      end if;

      --  Nothing to do if Expr is statically reclaimed (ie. stands for null)

      if (if Expr.Is_Ent
          then Is_Null_Or_Reclaimed_Obj (Expr.Ent, Reclaimed => True)
          else Is_Null_Or_Reclaimed_Expr (Expr.Expr, Reclaimed => True))
      then
         return;
      end if;

      --  Identify the root type for the path

      Root := Unique_Entity_In_SPARK (Root);

      --  Search for a call to a function annotated with At_End_Borrow
      --  either in the parents of Expr or inside Expr (as the function is
      --  a traversal function, it can be part of a path).

      if not Expr.Is_Ent then
         declare
            Call   : Node_Id := Get_Observed_Or_Borrowed_Expr (Expr.Expr);
            Brower : Entity_Id;
         begin
            loop
               Call := Parent (Call);

               if No (Call) or else Nkind (Call) not in N_Subexpr then
                  exit;

               --  If we have found such a call, do the permission checking on
               --  the borrower instead. There might be no borrower if the call
               --  is ill-formed.

               elsif Nkind (Call) = N_Function_Call
                 and then Has_At_End_Borrow_Annotation
                            (Get_Called_Entity (Call))
               then
                  Brower := Borrower_For_At_End_Borrow_Call (Call);
                  if Present (Brower) then
                     Process_Path
                       ((Is_Ent => True, Ent => Brower, Loc => Loc), Mode);
                  end if;
                  return;
               end if;
            end loop;
         end;
      end if;

      --  If root is saving a prophecy variable, walk back declaration chain
      --  to find initial At_End_Borrow call, and do the permission checking
      --  on the borrower instead.

      if Is_Prophecy_Save (Root) then
         declare
            N      : Node_Id := Expression (Parent (Root));
            Brower : Entity_Id;
         begin
            loop
               case Nkind (N) is
                  when N_Function_Call =>
                     pragma
                       Assert
                         (Has_At_End_Borrow_Annotation
                            (Get_Called_Entity (N)));
                     Brower := Borrower_For_At_End_Borrow_Call (N);
                     if Present (Brower) then
                        Process_Path
                          ((Is_Ent => True, Ent => Brower, Loc => Loc), Mode);
                     end if;
                     return;

                  when N_Selected_Component
                     | N_Indexed_Component
                     | N_Attribute_Reference
                     | N_Explicit_Dereference
                  =>
                     N := Prefix (N);

                  when N_Identifier | N_Expanded_Name =>
                     N := Expression (Parent (Entity (N)));

                  when others =>
                     --  Should be ruled out by marking.

                     raise Program_Error;
               end case;
            end loop;
         end;
      end if;

      --  Check path was not borrowed

      Check_Not_Borrowed (Expr, Root);

      --  For modes that require W permission, check path was not observed

      case Mode is
         when Read | Observe =>
            null;

         when Assign | Move | Free | Borrow =>
            Check_Not_Observed (Expr, Root);
      end case;

      --  If the root and target types are both not deep, this is a shallow
      --  assignment. The root could still be moved, but only if it is already
      --  in the permission environment. If we cannot find it, we can return
      --  early. This is a performance optimization to avoid putting
      --  permissions for shallow types in the environment when unnecessary.

      if not Is_Deep (Etype (Root))
        and then not Is_Deep (Expr_Type)
        and then Get (Current_Perm_Env, Root) = null
      then
         return;
      end if;

      --  Check that the root of the moved expression does not have overlays.
      --  We could also only consider visible overlays, or even move all
      --  overlays visible at this point in the program.

      if Mode = Move and then not Overlay_Alias (Root).Is_Empty then
         BC_Error
           (Create
              ("moved object aliased through address clauses is not supported"
               & " yet"),
            Loc);
      end if;

      if Query_Read_Only_Tree (Current_Perm_Env, Root) = null then

         --  If the root object is not in the current environment, then it must
         --  be a constant without variable input. It can only be read.

         if Ekind (Root) /= E_Constant
           or else Is_Access_Variable (Etype (Root))
           or else Has_Variable_Input (Root)
         then
            pragma Assert (Present (Current_Subp));
            BC_Error
              (Create
                 ("owning or observing object should occur in the global"
                  & " contract of &",
                  Names => [Current_Subp]),
               Root);
         end if;

         Perm := Read_Only;
         Expl := Root;
      else
         declare
            Perm_Expl : constant Perm_And_Expl := Get_Perm_And_Expl (Expr);
         begin
            Perm := Perm_Expl.Perm;
            Expl := Perm_Expl.Expl;
         end;
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
                  BC_Error (Create ("illegal move during elaboration"), Loc);
               end if;

               return;
            end if;

            --  Check read permissions of shallow parts

            if Perm not in Read_Perm then
               Perm_Error (Expr, Read_Only, Perm, Expl => Expl);
               return;
            end if;

            --  Check read-write permissions of parts reachable under
            --  dereference

            declare
               Perm_Expl : constant Perm_And_Expl :=
                 Get_Perm_And_Expl (Expr, Under_Dereference => True);
            begin
               --  SPARK RM 3.10(1): At the point of a move operation the state
               --  of the source object (if any) shall be Unrestricted.

               if Perm_Expl.Perm /= Read_Write then
                  Perm_Error
                    (Expr, Read_Write, Perm_Expl.Perm, Expl => Perm_Expl.Expl);
                  return;
               end if;
            end;

         when Free =>
            --  Check W permission on the pointed-to path. Still issue an error
            --  message wrt permission of the full path and RW permission, as
            --  it is likely less confusing.

            declare
               Perm_Expl : constant Perm_And_Expl :=
                 Get_Perm_And_Expl (Expr, Under_Dereference => True);
            begin
               if Perm_Expl.Perm not in Write_Perm then
                  Perm_Error
                    (Expr, Read_Write, Perm_Expl.Perm, Expl => Perm_Expl.Expl);
                  return;
               end if;
            end;

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

            --  For borrowing, check read-write on designated values

            declare
               Perm_Expl : constant Perm_And_Expl :=
                 Get_Perm_And_Expl (Expr, Under_Dereference => True);
            begin
               if Perm_Expl.Perm /= Read_Write then
                  Perm_Error
                    (Expr, Read_Write, Perm_Expl.Perm, Expl => Perm_Expl.Expl);
                  return;
               end if;
            end;

            --  Permission of borrowed path must be readable, as otherwise it
            --  should not be possible to read designated value.

            pragma Assert (Perm in Read_Perm);

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

      --  Do not update permission environment when handling calls, unless this
      --  is call to an instance of Unchecked_Deallocation for which Mode=Free.

      if Inside_Procedure_Call and then Mode /= Free then
         return;
      end if;

      --  Update the permissions

      case Mode is

         when Read =>
            null;

         when Free =>
            --  Set permission RW for the path and its extensions

            declare
               Tree : constant Perm_Tree_Access := Get_Perm_Tree (Expr);
            begin
               Tree.all.Tree.Permission := Read_Write;
               Set_Perm_Extensions (Tree, Read_Write, Expl => Loc);

               --  Normalize the permission tree

               Set_Perm_Prefixes_Assign (Expr);
            end;

         when Move =>

            --  SPARK RM 3.10(1): After a move operation, the state of the
            --  source object (if any) becomes Moved.

            if Present (Root) then
               declare
                  Is_Access : constant Boolean :=
                    not Expr.Is_Ent
                    and then Nkind (Expr.Expr) = N_Attribute_Reference;
                  pragma
                    Assert
                      (if Is_Access
                         then Attribute_Name (Expr.Expr) = Name_Access);
                  Tree      : constant Perm_Tree_Access :=
                    (if Is_Access
                     then
                       Set_Perm_Prefixes
                         (+Prefix (Expr.Expr),
                          No_Access,
                          Loc,
                          Move_Access => True)
                     else Set_Perm_Prefixes (Expr, Write_Only, Expl => Loc));
               begin
                  pragma Assert (Tree /= null);
                  if Is_Access then
                     Set_Perm_Extensions (Tree, No_Access, Expl => Loc);
                  else
                     Set_Perm_Extensions_Move (Tree, Expr_Type, Expl => Loc);
                  end if;
               end;
            end if;

         when Assign =>

            --  If there is no root object, or the tree has an array component,
            --  then the permissions do not get modified by the assignment.

            if No (Root)
              or else (not Expr.Is_Ent
                       and then Has_Array_Component (Expr.Expr))
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

   procedure Return_Globals (Subp : Entity_Id; Exceptional : Boolean := False)
   is

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
         pragma Unreferenced (Global_Var);
         pragma Unreferenced (Typ);
         pragma Unreferenced (Kind);
      begin
         Return_Parameter_Or_Global
           (Id => Expr.Ent, Subp => Subp, Exceptional => Exceptional);
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
     (Id : Entity_Id; Subp : Entity_Id; Exceptional : Boolean) is
   begin
      --  Ignore 'self' component of concurrent types. See
      --  Setup_Parameter_Or_Global for the explanation.

      if Ekind (Id) in E_Protected_Type | E_Task_Type then
         return;
      end if;

      declare
         Expected_Perm_Tree : constant not null Perm_Tree_Access :=
           Get (Default_Perm_Env, Id);
         Expected_Perm      : constant Perm_Kind :=
           Permission (Expected_Perm_Tree);
         Current_Perm_Tree  : constant Perm_Tree_Access :=
           Get (Current_Perm_Env, Id);
      begin

         --  Parameters and globals need not to be considered if they are not
         --  in the permission environment, as they keep their initial
         --  permissions. Neither is it needed if they were initially
         --  read-only, as then they cannot have been moved.

         if Current_Perm_Tree = null or else Expected_Perm = Read_Only then
            return;
         end if;

         --  All other parameters and globals should return with mode RW to the
         --  caller.

         pragma Assert (Expected_Perm = Read_Write);

         declare
            Perm : constant Perm_Kind := Permission (Current_Perm_Tree);
         begin
            if Perm /= Read_Write then
               Perm_Error_Subprogram_End
                 (E           => Id,
                  Subp        => Subp,
                  Found_Perm  => Perm,
                  Expl        => Explanation (Current_Perm_Tree),
                  Exceptional => Exceptional);
            end if;
         end;
      end;
   end Return_Parameter_Or_Global;

   -----------------------
   -- Return_Parameters --
   -----------------------

   procedure Return_Parameters
     (Subp : Entity_Id; Exceptional : Boolean := False)
   is
      Formal : Entity_Id;
   begin
      Formal := First_Formal (Subp);
      while Present (Formal) loop
         Return_Parameter_Or_Global
           (Id => Formal, Subp => Subp, Exceptional => Exceptional);
         Next_Formal (Formal);
      end loop;
   end Return_Parameters;

   ---------------------------------
   -- Return_Protected_Components --
   ---------------------------------

   procedure Return_Protected_Components (Subp : Entity_Id) is

      procedure Return_Component (Comp : Entity_Id);
      --  Return component of protected object

      ----------------------
      -- Return_Component --
      ----------------------

      procedure Return_Component (Comp : Entity_Id) is
      begin
         Return_Parameter_Or_Global
           (Id => Comp, Subp => Subp, Exceptional => False);
      end Return_Component;

      --  Local variables

      Typ : constant Entity_Id := Scope (Subp);
   begin
      --  The protected object is an implicit input of protected functions, and
      --  an implicit input-output of protected procedures and entries.
      pragma Assert (Ekind (Subp) in E_Procedure | E_Entry);

      declare
         Comp : Entity_Id := First_Component_Or_Discriminant (Typ);
      begin
         while Present (Comp) loop
            Return_Component (Comp);
            Next_Component_Or_Discriminant (Comp);
         end loop;
      end;

      declare
         Anon_Obj : constant Entity_Id := Anonymous_Object (Scope (Subp));
      begin
         if Present (Anon_Obj) then
            for Comp of Iter (Part_Of_Constituents (Anon_Obj)) loop
               Return_Component (Comp);
            end loop;
         end if;
      end;
   end Return_Protected_Components;

   -------------------------
   -- Set_Perm_Extensions --
   -------------------------

   procedure Set_Perm_Extensions
     (T : Perm_Tree_Access; P : Perm_Kind; Expl : Node_Id)
   is

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
      T.all.Tree :=
        Perm_Tree'
          (Kind                => Entire_Object,
           Is_Node_Deep        => Is_Node_Deep (T),
           Explanation         => Expl,
           Permission          => Permission (T),
           Children_Permission => P);
   end Set_Perm_Extensions;

   ------------------------------
   -- Set_Perm_Extensions_Move --
   ------------------------------

   procedure Set_Perm_Extensions_Move
     (T : Perm_Tree_Access; E : Entity_Id; Expl : Node_Id)
   is
      Check_Ty : Entity_Id := Retysp (E);
   begin
      if Is_Class_Wide_Type (Check_Ty) then
         Check_Ty := Get_Specific_Type_From_Classwide (Check_Ty);
      end if;

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
               when E_Array_Type | E_Array_Subtype =>
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
                     T.all.Tree :=
                       (Kind              => Array_Component,
                        Is_Node_Deep      => Is_Node_Deep (T),
                        Explanation       => Expl,
                        Permission        => Write_Only,
                        Bounds_Permission => Read_Write,
                        Get_Elem          => C);
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
                           C :=
                             new Perm_Tree_Wrapper'
                               (Tree =>
                                  (Kind                => Entire_Object,
                                   Is_Node_Deep        =>
                                     Is_Deep (Etype (Comp)),
                                   Explanation         => Expl,
                                   Permission          => Read_Write,
                                   Children_Permission => Read_Write));
                           Set_Perm_Extensions_Move (C, Etype (Comp), Expl);

                        --  Hidden components are never deep

                        else
                           C :=
                             new Perm_Tree_Wrapper'
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

                     --  If the type has an ownership annotation, add a fake
                     --  deep component for its hidden part.

                     if Has_Ownership_Annotation (Check_Ty) then
                        C :=
                          new Perm_Tree_Wrapper'
                            (Tree =>
                               (Kind                => Entire_Object,
                                Is_Node_Deep        => True,
                                Explanation         => Expl,
                                Permission          => No_Access,
                                Children_Permission => No_Access));

                        Perm_Tree_Maps.Set (Hashtbl, Check_Ty, C);
                     end if;

                     T.all.Tree :=
                       (Kind         => Record_Component,
                        Is_Node_Deep => Is_Node_Deep (T),
                        Explanation  => Expl,
                        Permission   => Write_Only,
                        Component    => Hashtbl);
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
            T.Tree.Bounds_Permission := Read_Write;

         when Record_Component =>
            declare
               C    : Perm_Tree_Access;
               Comp : Entity_Id;

            begin
               Comp := First_Component_Or_Discriminant (Check_Ty);
               while Present (Comp) loop
                  C :=
                    Perm_Tree_Maps.Get
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

               --  If the type has an ownership annotation, also update the
               --  fake deep component for its hidden part.

               if Has_Ownership_Annotation (Check_Ty) then
                  C := Perm_Tree_Maps.Get (Component (T), Check_Ty);
                  C.Tree.Permission := No_Access;
               end if;
            end;
      end case;
   end Set_Perm_Extensions_Move;

   -----------------------
   -- Set_Perm_Prefixes --
   -----------------------

   function Set_Perm_Prefixes
     (N           : Expr_Or_Ent;
      Perm        : Perm_Kind_Option;
      Expl        : Node_Id;
      Move_Access : Boolean := False) return Perm_Tree_Access
   is

      function Set_Perm_Prefixes
        (N : Entity_Id; Perm : Perm_Kind_Option) return Perm_Tree_Access;
      --  Set permission for an entity

      -----------------------
      -- Set_Perm_Prefixes --
      -----------------------

      function Set_Perm_Prefixes
        (N : Entity_Id; Perm : Perm_Kind_Option) return Perm_Tree_Access
      is
         E : constant Entity_Id := Unique_Entity_In_SPARK (N);
         C : constant Perm_Tree_Access :=
           Query_Mutable_Tree (Current_Perm_Env, E);
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
         when N_Expanded_Name | N_Identifier =>
            return Set_Perm_Prefixes (Entity (N.Expr), Perm);

         --  For a nonterminal path, we set the permission tree of its prefix,
         --  and then we extract from the returned pointer the subtree and
         --  assign an adequate permission to it, if unfolded. If folded,
         --  we unroll the tree one level.

         when N_Explicit_Dereference =>
            declare
               C : constant Perm_Tree_Access :=
                 Set_Perm_Prefixes
                   (+Prefix (N.Expr),
                    (if Move_Access then Write_Only else Perm),
                    Expl);
               pragma Assert (C /= null);
               pragma
                 Assert
                   (Kind (C) = Entire_Object or else Kind (C) = Reference);
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
                     D       : constant Perm_Tree_Access :=
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

                     C.all.Tree :=
                       (Kind            => Reference,
                        Is_Node_Deep    => Is_Node_Deep (C),
                        Explanation     => Expl,
                        Permission      => Permission (C),
                        Null_Permission => Child_P,
                        Get_All         => D);
                     return D;
                  end;
               end if;
            end;

         when N_Selected_Component =>
            declare
               C : constant Perm_Tree_Access :=
                 Set_Perm_Prefixes (+Prefix (N.Expr), Perm, Expl, Move_Access);
               pragma Assert (C /= null);
               pragma
                 Assert
                   (Kind (C) = Entire_Object
                      or else Kind (C) = Record_Component);
            begin
               --  The tree is already unfolded. Replace the permission of the
               --  component.

               if Kind (C) = Record_Component then
                  declare
                     Comp : constant Entity_Id :=
                       Original_Record_Component
                         (Entity (Selector_Name (N.Expr)));
                     D    : constant Perm_Tree_Access :=
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

                     Pref_Ty : Entity_Id := Retysp (Etype (Prefix (N.Expr)));
                     D       : Perm_Tree_Access;
                     D_This  : Perm_Tree_Access;
                     Comp    : Node_Id;
                     P       : Perm_Kind;
                     Child_P : constant Perm_Kind := Children_Permission (C);
                     Hashtbl : Perm_Tree_Maps.Instance;
                     --  Create an empty hash table

                  begin
                     if Is_Class_Wide_Type (Pref_Ty) then
                        Pref_Ty := Get_Specific_Type_From_Classwide (Pref_Ty);
                     end if;

                     Comp := First_Component_Or_Discriminant (Pref_Ty);

                     while Present (Comp) loop
                        if Perm /= None
                          and then Original_Record_Component (Comp)
                                   = Original_Record_Component
                                       (Entity (Selector_Name (N.Expr)))
                        then
                           P := Perm;
                        else
                           P := Child_P;
                        end if;

                        D :=
                          new Perm_Tree_Wrapper'
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

                        if Original_Record_Component (Comp)
                          = Original_Record_Component
                              (Entity (Selector_Name (N.Expr)))
                        then
                           D_This := D;
                        end if;

                        Next_Component_Or_Discriminant (Comp);
                     end loop;

                     --  If the type has an ownership annotation, add a fake
                     --  deep component for its hidden part.

                     if Has_Ownership_Annotation (Pref_Ty) then
                        if Perm /= None then
                           P := Perm;
                        else
                           P := Child_P;
                        end if;

                        D :=
                          new Perm_Tree_Wrapper'
                            (Tree =>
                               (Kind                => Entire_Object,
                                Is_Node_Deep        => True,
                                Explanation         => Expl,
                                Permission          => P,
                                Children_Permission => Child_P));
                        Perm_Tree_Maps.Set (Hashtbl, Pref_Ty, D);
                     end if;

                     C.all.Tree :=
                       (Kind         => Record_Component,
                        Is_Node_Deep => Is_Node_Deep (C),
                        Explanation  => Expl,
                        Permission   => Permission (C),
                        Component    => Hashtbl);
                     return D_This;
                  end;
               end if;
            end;

         when N_Indexed_Component =>
            declare
               C : constant Perm_Tree_Access :=
                 Set_Perm_Prefixes (+Prefix (N.Expr), Perm, Expl, Move_Access);
               pragma Assert (C /= null);
               pragma
                 Assert
                   (Kind (C) = Entire_Object
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
                     D       : constant Perm_Tree_Access :=
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

                     C.all.Tree :=
                       (Kind              => Array_Component,
                        Is_Node_Deep      => Is_Node_Deep (C),
                        Explanation       => Expl,
                        Permission        => Permission (C),
                        Bounds_Permission => Child_P,
                        Get_Elem          => D);
                     return D;
                  end;
               end if;
            end;

         when N_Slice =>
            return
              Set_Perm_Prefixes (+Prefix (N.Expr), Perm, Expl, Move_Access);

         when N_Qualified_Expression
            | N_Type_Conversion
            | N_Unchecked_Type_Conversion
         =>
            return
              Set_Perm_Prefixes
                (+Expression (N.Expr), Perm, Expl, Move_Access);

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

            when N_Expanded_Name | N_Identifier =>
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
         pragma Unreferenced (Typ);

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
         if Is_Subprogram_Or_Entry (Scop) or Is_Task_Type (Scop) then
            Pragma_Node := Find_Contract (Scop, Pragma_Global);
            if No (Pragma_Node) then
               Pragma_Node := Find_Contract (Scop, Pragma_Depends);
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
            Flow_Utility.Get_Proof_Globals
              (Subprogram      => Scop,
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
      Kind       : Formal_Kind;
      Subp       : Entity_Id;
      Global_Var : Boolean;
      Expl       : Node_Id)
   is
      Perm : Perm_Kind_Option;

   begin
      --  We do not handle task types/protected types directly in the
      --  borrow-checker. Rather, their dependent entities (fields of protected
      --  objects for instance) are used directly as roots.

      if Ekind (Id) in E_Task_Type | E_Protected_Type then
         return;
      end if;

      --  By default, we use the permission corresponding to the declaration.
      --  We branch for special cases where the starting permissions may depend
      --  on the context (globals and protected component).

      --  For global variables, we normally use the mode given by the contract.
      --  However, if the contract was generated, we prefer using the
      --  permission of the declaration to have better error messages. The
      --  problematic case is a global variable which is moved by the
      --  subprogram, but is only read so flow analysis tags it as a global
      --  input. It seems clearer to complain at the end of the scope when the
      --  variable is not assigned back, than to emit a strange message stating
      --  that the variable was declared as read-only by a flow generated
      --  contract.

      if Global_Var
        and then (Is_Subprogram_Or_Entry (Subp) or else Is_Task_Type (Subp))
        and then Present (Find_Contract (Subp, Pragma_Global))
      then
         Perm := (if Kind = E_In_Parameter then Read_Only else Read_Write);

      --  Components of protected types are read-only for their functions,
      --  and read-write otherwise

      elsif Within_Protected_Type (Subp)
        and then Is_Protected_Component_Or_Discr_Or_Part_Of (Id)
      then
         Perm := (if Ekind (Subp) = E_Function then Read_Only else Read_Write);

      --  In all other cases, the context does not affect starting permission

      else
         Perm := (if Is_Read_Only (Id) then Read_Only else Read_Write);
      end if;

      Setup_Environment_For_Object (Id, Perm, Expl);
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

      procedure Setup_Component (Comp : Entity_Id; Kind : Formal_Kind);
      --  Setup for component of protected object

      ---------------------
      -- Setup_Component --
      ---------------------

      procedure Setup_Component (Comp : Entity_Id; Kind : Formal_Kind) is
      begin
         Setup_Parameter_Or_Global
           (Id         => Comp,
            Kind       => Kind,
            Subp       => Subp,
            Global_Var => False,
            Expl       => Comp);
      end Setup_Component;

      --  Local variables

      Typ  : constant Entity_Id := Scope (Subp);
      Kind : Formal_Kind;

   begin
      --  The protected object is an implicit input of protected functions, and
      --  an implicit input-output of protected procedures and entries.

      if Ekind (Subp) = E_Function then
         Kind := E_In_Parameter;
      else
         Kind := E_In_Out_Parameter;
      end if;

      declare
         Comp : Entity_Id := First_Component_Or_Discriminant (Typ);
      begin
         while Present (Comp) loop
            Setup_Component (Comp, Kind);
            Next_Component_Or_Discriminant (Comp);
         end loop;
      end;

      declare
         Anon_Obj : constant Entity_Id := Anonymous_Object (Scope (Subp));
      begin
         if Present (Anon_Obj) then
            for Comp of Iter (Part_Of_Constituents (Anon_Obj)) loop
               Setup_Component (Comp, Kind);
            end loop;
         end if;
      end;
   end Setup_Protected_Components;

end Gnat2Why.Borrow_Checker;
