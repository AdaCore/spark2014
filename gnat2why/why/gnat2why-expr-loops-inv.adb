------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--               G N A T 2 W H Y - E X P R - L O O P S - I N V              --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                    Copyright (C) 2016-2017, AdaCore                      --
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

with Ada.Text_IO;
with Ada.Unchecked_Deallocation;
with Common_Containers;
with Flow_Utility;           use Flow_Utility;
with Nlists;                 use Nlists;
with Gnat2Why.Tables;        use Gnat2Why.Tables;
with Sem_Aux;                use Sem_Aux;
with Sem_Util;               use Sem_Util;
with Snames;                 use Snames;
with SPARK_Util.Types;       use SPARK_Util.Types;
with Why;                    use Why;
with Why.Atree.Builders;     use Why.Atree.Builders;
with Why.Atree.Modules;      use Why.Atree.Modules;
with Why.Conversions;        use Why.Conversions;
with Why.Gen.Arrays;         use Why.Gen.Arrays;
with Why.Gen.Binders;        use Why.Gen.Binders;
with Why.Gen.Expr;           use Why.Gen.Expr;
with Why.Gen.Names;          use Why.Gen.Names;
with Why.Gen.Preds;          use Why.Gen.Preds;
with Why.Gen.Records;        use Why.Gen.Records;
with Why.Gen.Terms;          use Why.Gen.Terms;

package body Gnat2Why.Expr.Loops.Inv is

   type Write_Kind is
     (Entire_Object, Record_Components, Array_Components, Discard);
   --  The status of a variable or a part of a variable.
   --   * Entire_Object the object is entirely written.
   --   * Record_Components some fields (maybe all) of the record object are
   --                   written.
   --   * Array_Components  some indexes (maybe all) of the array object are
   --                   written.
   --   * Discard       we don't care about the variable and won't output any
   --                   invariant for it (typically for local variables).

   type Write_Status;
   type Write_Status_Access is access all Write_Status;

   package Write_Status_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Write_Status_Access,
      Hash            => Common_Containers.Node_Hash,
      Equivalent_Keys => "=");
   use Write_Status_Maps;

   package Array_Constraints_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Boolean,
      Hash            => Common_Containers.Node_Hash,
      Equivalent_Keys => "=");

   type Write_Status (Kind : Write_Kind) is limited record
      case Kind is
         when Entire_Object | Discard => null;
         when Record_Components =>
            Component_Status  : Write_Status_Maps.Map;
         when Array_Components  =>
            Write_Constraints : Array_Constraints_Maps.Map;
            Content_Status    : Write_Status_Access;
      end case;
   end record;
   --  If only some parts of the object are written, we store their write
   --  status in Write_Status additional fields. To keep track of which array
   --  indexes are written, we store array writes in the Write_Constraints
   --  field. We map them to a boolean which is True if the loop invariant has
   --  already been encountered when the update occurs and False otherwise.

   function Equality_Of_Preserved_Components
     (Loop_Idx  : Entity_Id;
      Is_Rev    : Boolean;
      Var_Known : Boolean;
      Loop_Vars : Flow_Id_Sets.Set;
      Expr      : W_Expr_Id;
      At_Entry  : W_Expr_Id;
      Expr_Ty   : Entity_Id;
      Status    : in out Write_Status_Access)
      return W_Pred_Id
   with
     Pre => Status /= null and then Status.Kind /= Discard;
   --  Compute a predicate which assumes preservation of every unmodified
   --  part of an expression. Status is finalized by the call for sanity
   --  checking purpose.
   --  @param Loop_Idx Ada entity of the loop index if any
   --  @param Is_Rev True if the loop is reversed
   --  @param Var_Known True if flow analysis was run and Loop_Vars is
   --         populated.
   --  @param Loop_Vars set of Flow_Ids modified by the loop statement
   --  @param Expr Why expression at the current loop index
   --  @param At_Entry Why expression at the loop's entry
   --  @param Expr_Ty Ada type of Expr
   --  @param Status Write_Status of Expr
   --  @return a predicate stating that fields not written in Status are equal
   --          in Expr and At_Entry.

   -------------------------------------------
   -- Construction of the Write_Status_Maps --
   -------------------------------------------

   procedure Finalize (Status : in out Write_Status_Access);
   --  Free the memory for Status and set it to null.
   --  @param Status the write status to be freed.

   function New_Status
     (New_Write      : Entity_Id;
      Discard_Writes : Boolean;
      Expected_Kind  : Write_Kind)
      return Write_Status_Access
   with
     Pre => Expected_Kind /= Discard;
   --  Create a Write_Status for New_Write.
   --  @param New_Write variable or record field to which we are writing.
   --  @param Discard_Writes True if the writes to the variable should be
   --         discarded.
   --  @param Expected_Kind expected kind of the updated status.
   --  @result an access to a fresh status for New_Write.

   procedure One_Level_Update
     (New_Write      : Entity_Id;
      Loop_Writes    : in out Write_Status_Maps.Map;
      Discard_Writes : Boolean;
      Expected_Kind  : Write_Kind;
      Updated_Status : out Write_Status_Access)
   --  Update New_Write's write status in Loop_Writes.
   --  @param New_Write variable or record field to be added to Loop_Writes.
   --  @param Loop_Writes map between entities and their write status.
   --  @param Discard_Writes True if the writes to the variable should be
   --         discarded.
   --  @param Expected_Kind expected kind of the updated status.
   --  @param Updated_Status access to New_Write's write status.

   with
     Pre  => Expected_Kind /= Discard,
     Post => Updated_Status /= null
       and then Loop_Writes.Contains (New_Write)
       and then Updated_Status = Loop_Writes.Element (New_Write)
       and then (if Discard_Writes then
                   Loop_Writes.Element (New_Write).Kind = Discard
                 elsif Expected_Kind = Entire_Object then
                   Loop_Writes.Element (New_Write).Kind in
                     Discard | Entire_Object),
     Contract_Cases =>
       --  When marked as discarded, a variable or record field stays
       --  discarded, as its write status does not matter.
       (Loop_Writes.Contains (New_Write)
          and then Loop_Writes.Element (New_Write).Kind = Discard
        =>
          Loop_Writes.Element (New_Write).Kind = Discard,
        --  Entire variables of record fields should still be considered wholly
        --  after the assignment.
        Loop_Writes.Contains (New_Write)
          and then Loop_Writes.Element (New_Write).Kind = Entire_Object
        =>
          Loop_Writes.Element (New_Write).Kind in Discard | Entire_Object,
        others => True);

   procedure One_Level_Update
     (New_Write      : Entity_Id;
      Loop_Writes    : in out Write_Status_Maps.Map;
      Discard_Writes : Boolean);
   --  Same as before except that Expected_Kind is set to Entire_Object and
   --  Updated_Status is discarded.

   procedure Update_Status
     (New_Write      : Node_Id;
      Loop_Writes    : in out Write_Status_Maps.Map;
      Inv_Seen       : Boolean;
      Expected_Kind  : Write_Kind;
      Expected_Type  : out Entity_Id;
      Updated_Status : out Write_Status_Access)
   with
     Pre  => Expected_Kind /= Discard,
     Post => Updated_Status /= null;
   --  Update a write status map to account for a new write. It may require
   --  several updates if New_Write is a complex variable name.
   --  @param New_Write variable name which has been written.
   --  @param Loop_Writes map between entities and their write status.
   --  @param Inv_Seen True if the current update occurs after the loop
   --         invariant in the top level loop.
   --  @param Expected_Kind expected kind of the updated status.
   --  @param Expected_Type type of the actual updated object part.
   --  @param Updated_Status access to New_Write's write status.

   procedure Update_Status
     (New_Write   : Node_Id;
      Loop_Writes : in out Write_Status_Maps.Map;
      Inv_Seen    : Boolean);
   --  Same as before except that Expected_Kind is set to Entire_Object and
   --  Expected_Type and Updated_Status are discarded.

   --------------------
   -- Tree Traversal --
   --------------------

   function Get_Loop_Writes
     (Loop_Stmt          : Node_Id;
      Has_Loop_Invariant : Boolean)
      return Write_Status_Maps.Map;
   --  Traverse a loop statement and accumulate potentially written variables.
   --  @param Loop_Stmt considered loop statement.
   --  @param Has_Loop_Invariant True iff the loop has a loop invariant.
   --  @return a map between written entities and their write status.

   procedure Process_Call_Statement
     (Call        : Node_Id;
      Loop_Writes : in out Write_Status_Maps.Map;
      Inv_Seen    : Boolean);
   --  Update a status map for every variable written by a call statement.
   --  @param Call considered call statement.
   --  @param Loop_Writes a map between written entities and their write
   --         status.
   --  @param Inv_Seen True if the statement occurs after the loop invariant
   --         in the top level loop.

   procedure Process_Loop_Statement
     (Loop_Stmt   : Node_Id;
      Loop_Writes : in out Write_Status_Maps.Map;
      Inv_Seen    : Boolean;
      In_Nested   : Boolean);
   --  Traverse a loop statement and update a status map for every variable
   --  potentially written by the loop.
   --  @param Loop_Stmt considered loop statement.
   --  @param Loop_Writes a map between written entities and their write
   --         status.
   --  @param Inv_Seen True if the statement occurs after the loop invariant
   --         in the top level loop.
   --  @param In_Nested True if the statement occurs inside a nested statement.

   procedure Process_Statement
     (N           : Node_Id;
      Loop_Writes : in out Write_Status_Maps.Map;
      Inv_Seen    : Boolean;
      In_Nested   : Boolean);
   --  Traverse a statement and update a status map for every variable
   --  potentially written by the statement.
   --  @param N considered statement.
   --  @param Loop_Writes a map between written entities and their write
   --         status.
   --  @param Inv_Seen True if the statement occurs after the loop invariant
   --         in the top level loop.
   --  @param In_Nested True if the statement occurs inside a nested statement.

   procedure Process_Statement_List
     (L           : List_Id;
      Loop_Writes : in out Write_Status_Maps.Map;
      Inv_Seen    : Boolean;
      In_Nested   : Boolean);
   --  Process every statement of a list.
   --  @param L considered list of statements.
   --  @param Loop_Writes a map between written entities and their write
   --         status.
   --  @param Inv_Seen True if the statement occurs after the loop invariant
   --         in the top level loop.
   --  @param In_Nested True if the statement occurs inside a nested statement.

   --------------------------------------
   -- Equality_Of_Preserved_Components --
   --------------------------------------

   function Equality_Of_Preserved_Components
     (Loop_Idx  : Entity_Id;
      Is_Rev    : Boolean;
      Var_Known : Boolean;
      Loop_Vars : Flow_Id_Sets.Set;
      Expr      : W_Expr_Id;
      At_Entry  : W_Expr_Id;
      Expr_Ty   : Entity_Id;
      Status    : in out Write_Status_Access)
      return W_Pred_Id
   is
      Preserved_Components : W_Pred_Id := True_Pred;

      function Build_Array_Constraints
        (Updates : Array_Constraints_Maps.Map;
         Indices : W_Expr_Array)
         return W_Pred_Id;
      --  Generate an approximation of the set of preserved indexes in an
      --  array from the set of all its updates in the loop statement.

      procedure Handle_Record_Component (Component : Entity_Id);
      --  Generate the appropriate equality if the field is preserved and call
      --  Equality_Of_Preserved_Components recursively otherwise.

      function Build_Array_Constraints
        (Updates : Array_Constraints_Maps.Map;
         Indices : W_Expr_Array)
         return W_Pred_Id
      is
         function Is_Constant (Expr : Node_Id) return Boolean is
           (Var_Known
            and then Get_Variables_For_Proof (Expr, Expr).Intersection
            (Loop_Vars).Is_Empty);
         --  Check whether an expression is constant in the loop statement. If
         --  the variables modified in the loop are not known, assume nothing
         --  is constant.

         function Is_Loop_Idx (Expr : Node_Id) return Boolean is
           (Present (Loop_Idx)
            and then Nkind (Expr) in N_Identifier | N_Expanded_Name
            and then Entity (Expr) = Loop_Idx);
         --  Check whether an expression is the loop index

         function Mk_Lt
           (Left, Right : W_Expr_Id;
            Typ         : W_Type_Id;
            Or_Eq       : Boolean := False) return W_Pred_Id;
         --  Create a comparison between Left and Right. If Or_Eq is True, the
         --  operator is <= else it is <.

         -----------
         -- Mk_Lt --
         -----------

         function Mk_Lt
           (Left, Right : W_Expr_Id;
            Typ         : W_Type_Id;
            Or_Eq       : Boolean := False) return W_Pred_Id
         is
            Symb : constant W_Identifier_Id :=
              (if Typ = EW_Int_Type
               then (if Or_Eq then Int_Infix_Le else Int_Infix_Lt)
               elsif Why_Type_Is_BitVector (Typ)
               then (if Or_Eq then MF_BVs (Typ).Ule
                 else MF_BVs (Typ).Ult)
               else raise Program_Error);
         begin
            return +New_Comparison (Symb, Left, Right, EW_Pred);
         end Mk_Lt;

         use Array_Constraints_Maps;
         Constraints : W_Pred_Id := True_Pred;

      begin
         --  Iterate over the set of writes to array components and generate a
         --  predicate representing cases where we are sure that the array is
         --  not written. All the cases are joined using 'and' connectors.

         for C in Updates.Iterate loop
            declare
               Update   : constant Node_Id := Key (C);
               Inv_Seen : constant Boolean := Element (C);
            begin
               if Nkind (Update) = N_Slice then
                  pragma Assert (Indices'Length = 1);

                  --  The assignment is a slice. There can be several cases
                  --  for which we know the components are preserved. Link them
                  --  with 'or' connectors.

                  declare
                     Rng        : constant Node_Id :=
                       Get_Range (Discrete_Range (Update));
                     Low        : constant Node_Id := Low_Bound (Rng);
                     High       : constant Node_Id := High_Bound (Rng);
                     Typ        : constant W_Type_Id := Get_Type (Indices (1));
                     Constraint : W_Pred_Id := False_Pred;

                  begin
                     --  If Low is constant, generate I < Low

                     if Is_Constant (Low) then
                        Constraint :=
                          +New_Or_Else_Expr
                          (Left   => +Mk_Lt
                             (Left   => Indices (1),
                              Right  => Transform_Expr
                                (Expr          => Low,
                                 Domain        => EW_Term,
                                 Params        => Body_Params,
                                 Expected_Type => Typ),
                              Typ    => Typ),
                           Right  => +Constraint,
                           Domain => EW_Pred);

                     --  If the loop is reversed and Low is Loop_Idx, generate
                     --  I < Low if the statement occurs before the invariant
                     --  and I <= Low otherwise.

                     elsif Is_Rev and then Is_Loop_Idx (Low) then
                        Constraint :=
                          +New_Or_Else_Expr
                          (Left   => +Mk_Lt
                             (Left   => Indices (1),
                              Right  => Transform_Expr
                                (Expr          => Low,
                                 Domain        => EW_Term,
                                 Params        => Body_Params,
                                 Expected_Type => Typ),
                              Typ    => Typ,
                              Or_Eq  => Inv_Seen),
                           Right  => +Constraint,
                           Domain => EW_Pred);
                     end if;

                     --  If High is constant, generate High < I

                     if  Is_Constant (High) then
                        Constraint :=
                          +New_Or_Else_Expr
                          (Left   => +Mk_Lt
                             (Left   => Transform_Expr
                                (Expr          => High,
                                 Domain        => EW_Term,
                                 Params        => Body_Params,
                                 Expected_Type => Typ),
                              Right  => Indices (1),
                              Typ    => Typ),
                           Right  => +Constraint,
                           Domain => EW_Pred);

                     --  If the loop is not reversed and High is Loop_Idx
                     --  generate High < I if the statement occurs before the
                     --  invariant and High <= I otherwise.

                     elsif not Is_Rev and then Is_Loop_Idx (High) then
                        Constraint :=
                          +New_Or_Else_Expr
                          (Left   => +Mk_Lt
                             (Left   => Transform_Expr
                                (Expr          => High,
                                 Domain        => EW_Term,
                                 Params        => Body_Params,
                                 Expected_Type => Typ),
                              Right  => Indices (1),
                              Typ    => Typ,
                              Or_Eq  => Inv_Seen),
                           Right  => +Constraint,
                           Domain => EW_Pred);
                     end if;

                     Constraints := +New_And_Then_Expr
                       (Left   => +Constraint,
                        Right  => +Constraints,
                        Domain => EW_Pred);
                  end;
               else

                  --  The assignment is a indexed component. Loop through the
                  --  array indices to generate cases in which we know the
                  --  components are preserved. Link them with 'or' connectors.

                  declare
                     Expression : Node_Id := First (Expressions (Update));
                     Constraint : W_Pred_Id := False_Pred;
                  begin
                     for I in Indices'Range loop
                        pragma Assert (Present (Expression));

                        declare
                           Typ  : constant W_Type_Id := Get_Type (Indices (I));
                           Expr : constant W_Expr_Id :=
                             Transform_Expr
                               (Expr          => Expression,
                                Domain        => EW_Term,
                                Params        => Body_Params,
                                Expected_Type => Typ);

                        begin
                           --  If Expression is Loop_Idx, generate:
                           --  - I < Expr if the iteration is reversed and the
                           --        statement occurs before the invariant,
                           --  - I <= Expr if the iteration is reversed and
                           --        the statement occurs after the invariant,
                           --  - Expr < I if the iteration is not reversed and
                           --        the statement occurs before the invariant,
                           --  - Expr <= I if the iteration is not reversed and
                           --        the statement occurs after the invariant.

                           if Is_Loop_Idx (Expression) then
                              if Is_Rev then
                                 Constraint :=
                                   +New_Or_Else_Expr
                                   (Left   => +Mk_Lt
                                      (Left   => Indices (I),
                                       Right  => Expr,
                                       Typ    => Typ,
                                       Or_Eq  => Inv_Seen),
                                    Right  => +Constraint,
                                    Domain => EW_Pred);
                              else
                                 Constraint :=
                                   +New_Or_Else_Expr
                                   (Left   => +Mk_Lt
                                      (Left   => Expr,
                                       Right  => Indices (I),
                                       Typ    => Typ,
                                       Or_Eq  => Inv_Seen),
                                    Right  => +Constraint,
                                    Domain => EW_Pred);
                              end if;

                           --  If Expression is constant, generate I /= Expr

                           elsif Is_Constant (Expression) then
                              Constraint :=
                                +New_Or_Else_Expr
                                (Left   => New_Comparison
                                   (Symbol => Why_Neq,
                                    Left   => Expr,
                                    Right  => Indices (I),
                                    Domain => EW_Pred),
                                 Right  => +Constraint,
                                 Domain => EW_Pred);
                           end if;
                        end;
                        Expression := Next (Expression);
                     end loop;

                     Constraints := +New_And_Then_Expr
                       (Left   => +Constraint,
                        Right  => +Constraints,
                        Domain => EW_Pred);
                  end;
               end if;
            end;
         end loop;
         return Constraints;
      end Build_Array_Constraints;

      procedure Handle_Record_Component (Component : Entity_Id) is
         F_Expr_Ty  : constant Entity_Id :=
           Retysp (Etype (Component));
         F_Expr     : constant W_Expr_Id :=
           New_Ada_Record_Access (Ada_Node => Empty,
                                  Name     => Expr,
                                  Domain   => EW_Term,
                                  Field    => Component,
                                  Ty       => Expr_Ty);
         F_At_Entry : constant W_Expr_Id :=
           New_Ada_Record_Access (Ada_Node => Empty,
                                  Name     => At_Entry,
                                  Domain   => EW_Term,
                                  Field    => Component,
                                  Ty       => Expr_Ty);
         Inv        : W_Pred_Id;

      begin
         --  Component is modified

         if Status.Component_Status.Contains (Component) then

            declare
               F_Status : Write_Status_Access :=
                 Status.Component_Status.Element (Component);
            begin

               --  Look for its preserved subfields

               Inv := Equality_Of_Preserved_Components
                 (Loop_Idx  => Loop_Idx,
                  Is_Rev    => Is_Rev,
                  Var_Known => Var_Known,
                  Loop_Vars => Loop_Vars,
                  Expr      => F_Expr,
                  At_Entry  => F_At_Entry,
                  Expr_Ty   => F_Expr_Ty,
                  Status    => F_Status);
            end;

            --  Remove visited fields for sanity checking

            Status.Component_Status.Exclude (Component);

            --  Component is preserved

         else
            Inv := +New_Comparison (Symbol => Why_Eq,
                                    Left   => F_Expr,
                                    Right  => F_At_Entry,
                                    Domain => EW_Pred);
         end if;

         Preserved_Components :=
           +New_And_Expr (Left   => +Preserved_Components,
                          Right  => +Inv,
                          Domain => EW_Pred);
      end Handle_Record_Component;

   --  Start of processing for Equality_Of_Preserved_Components

   begin
      case Status.Kind is
         when Discard =>
            raise Program_Error;

         when Entire_Object =>
            Preserved_Components := True_Pred;

         when Record_Components =>

            --  As discriminants may occur in bounds of types of other fields,
            --  store them in the Symbol_Table.

            Ada_Ent_To_Why.Push_Scope (Symbol_Table);

            declare
               Discrs  : constant Natural := Count_Discriminants (Expr_Ty);
               Discr   : Node_Id :=
                 (if Discrs > 0 then First_Discriminant (Expr_Ty)
                  else Empty);
               Tmps    : W_Identifier_Array (1 .. Discrs);
               Binds   : W_Expr_Array (1 .. Discrs);
               I       : Positive := 1;
            begin

               while Present (Discr) loop
                  if Is_Not_Hidden_Discriminant (Discr) then
                     Tmps (I) := New_Temp_Identifier
                       (Discr, EW_Abstract (Etype (Discr)));
                     Binds (I) := New_Ada_Record_Access
                       (Empty, EW_Term, Expr, Discr, Expr_Ty);

                     Insert_Entity (Discr, Tmps (I));

                     --  Only consider fields which are mutable, hence not
                     --  discriminants of types without default discriminants
                     --  or of constrained types.

                     if Discrs > 0 and then not Is_Constrained (Expr_Ty) then
                        Handle_Record_Component (Discr);
                     end if;
                  end if;

                  Next_Discriminant (Discr);
                  I := I + 1;
               end loop;

               for Component of Get_Component_Set (Expr_Ty) loop

                  --  Only consider fields which are visible in Expr_Ty.

                  if Component_Is_Visible_In_Type (Expr_Ty, Component) then
                     Handle_Record_Component (Component);
                  end if;
               end loop;

               --  Introduce bindings for the discriminants if any

               if Preserved_Components /= True_Pred then
                  for I in 1 .. Discrs loop
                     Preserved_Components := +New_Typed_Binding
                       (Domain  => EW_Pred,
                        Name    => Tmps (I),
                        Def     => Binds (I),
                        Context => +Preserved_Components);
                  end loop;
               end if;
            end;

            Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

            --  Sanity checking: all the non-visited fields are discarded

            pragma Assert (for all E of Status.Component_Status =>
                             E.Kind = Discard);

         --  For arrays, generate:
         --  forall i1 .. in : int. in_range i1 /\ .. /\ in_range in ->
         --    (if Array_Constraints i1 ... in
         --     then get <Expr> i1 .. in = get <At_Entry> i1 .. in
         --     else Equality_Of_Preserved_Components (get <Expr> i1 .. in))

         when Array_Components =>
            declare
               Dim        : constant Positive :=
                 Positive (Number_Dimensions (Expr_Ty));
               Vars       : Binder_Array (1 .. Dim);
               Indices    : W_Expr_Array (1 .. Dim);
               Range_Expr : W_Pred_Id := True_Pred;
               Index      : Node_Id := First_Index (Expr_Ty);
               I          : Positive := 1;
               Tmp        : W_Identifier_Id;

            begin
               while Present (Index) loop
                  Tmp := New_Temp_Identifier
                    (Typ => Base_Why_Type_No_Bool (Index));
                  Vars (I) := Binder_Type'(Ada_Node => Empty,
                                           B_Name   => Tmp,
                                           B_Ent    => Null_Entity_Name,
                                           Mutable  => False);
                  Indices (I) := +Tmp;
                  Range_Expr := +New_And_Expr
                    (Left   => +Range_Expr,
                     Right  =>
                       New_Array_Range_Expr (+Tmp, +Expr, EW_Pred, I),
                     Domain => EW_Pred);
                  Next_Index (Index);
                  I := I + 1;
               end loop;

               pragma Assert (I = Indices'Last + 1);

               declare
                  E_Expr_Ty        : constant Entity_Id :=
                    Retysp (Component_Type (Expr_Ty));
                  E_Expr           : constant W_Expr_Id :=
                    New_Array_Access (Empty, Expr, Indices, EW_Term);
                  E_At_Entry       : constant W_Expr_Id :=
                    New_Array_Access (Empty, At_Entry, Indices, EW_Term);
                  Constraints      : constant W_Pred_Id :=
                    Build_Array_Constraints
                      (Status.Write_Constraints, Indices);
                  Component_Status : W_Pred_Id :=
                    +New_Simpl_Conditional
                    (Domain    => EW_Pred,
                     Condition => +Constraints,
                     Then_Part =>
                       +New_Comparison (Symbol => Why_Eq,
                                        Left   => E_Expr,
                                        Right  => E_At_Entry,
                                        Domain => EW_Pred),
                     Else_Part =>
                       +Equality_Of_Preserved_Components
                       (Loop_Idx  => Loop_Idx,
                        Is_Rev    => Is_Rev,
                        Loop_Vars => Loop_Vars,
                        Var_Known => Var_Known,
                        Expr      => E_Expr,
                        At_Entry  => E_At_Entry,
                        Expr_Ty   => E_Expr_Ty,
                        Status    => Status.Content_Status));
               begin
                  if +Component_Status /= True_Pred then
                     Component_Status := New_Conditional
                       (Condition => +Range_Expr,
                        Then_Part => +Component_Status,
                        Typ       => EW_Bool_Type);

                     Preserved_Components := New_Universal_Quantif
                       (Binders => Vars,
                        Pred    => +Component_Status);
                  end if;
               end;
            end;
      end case;
      Finalize (Status);
      return Preserved_Components;
   end Equality_Of_Preserved_Components;

   --------------
   -- Finalize --
   --------------

   procedure Finalize (Status : in out Write_Status_Access) is
      procedure Free is
        new Ada.Unchecked_Deallocation (Write_Status, Write_Status_Access);
   begin
      if Status = null then
         return;
      end if;

      case Status.Kind is
         when Entire_Object
            | Discard
         =>
            null;
         when Record_Components =>
            for E of Status.Component_Status loop
               Finalize (E);
            end loop;
         when Array_Components   =>
            Finalize (Status.Content_Status);
      end case;

      Free (Status);
   end Finalize;

   ------------------------------
   -- Generate_Frame_Condition --
   ------------------------------

   function Generate_Frame_Condition
     (Loop_Stmt          : Node_Id;
      Has_Loop_Invariant : Boolean)
      return W_Pred_Id
   is
      Loop_Writes   : constant Map :=
        Get_Loop_Writes (Loop_Stmt, Has_Loop_Invariant);
      Loop_Id       : constant Entity_Id := Entity (Identifier (Loop_Stmt));
      Param_Spec    : constant Node_Id :=
        (if Present (Iteration_Scheme (Loop_Stmt))
         then Loop_Parameter_Specification (Iteration_Scheme (Loop_Stmt))
         else Empty);
      Loop_Index    : constant Entity_Id :=
        (if Present (Param_Spec) then Defining_Identifier (Param_Spec)
         else Empty);
      Is_Reverse    : constant Boolean :=
        Present (Param_Spec)
        and then Reverse_Present (Param_Spec);
      Scope         : constant Entity_Id := Enclosing_Unit (Loop_Id);
      Modified      : constant Flow_Id_Sets.Set :=
        (if Loop_Writes_Known (Loop_Id)
         then To_Entire_Variables (Flow_Utility.Get_Loop_Writes (Loop_Id))
         else Flow_Id_Sets.Empty_Set);
      N             : Node_Id;
      Dyn_Types_Inv : W_Pred_Id := True_Pred;

   begin
      --  Sanity checking:
      --  Check that we have at least every variable modified in the loop.

      if Loop_Writes_Known (Loop_Id) then
         for F of Modified loop

            --  We do not care about Magic_Strings which are translated as
            --  private in Why.

            if F.Kind = Direct_Mapping then

               --  We don't care about constant objects and objects
               --  with asynchronous readers as we don't want to assume
               --  anything on them. We also don't consider abstract
               --  states.
               --  For loops inside a single task, flow analysis returns the
               --  task object as written. We don't care as single
               --  tasks can't have (mutable) discriminants and thus cannot
               --  be modified from a proof point of view. We still want to
               --  issue an error if flow analysis returns a task with
               --  mutable discriminants that we did not find.

               declare
                  E : constant Entity_Id := Get_Direct_Mapping_Id (F);
               begin
                  if not Loop_Writes.Contains (E)
                    and then Is_Object (E)
                    and then Is_Mutable_In_Why (E)
                    and then not Has_Async_Writers (F)
                    and then
                      (not Is_Task_Type (Etype (E))
                       or else Count_Discriminants (Etype (E)) > 0)
                  then
                     Ada.Text_IO.Put_Line
                       ("error in computation of loop frame condition for "
                        & Full_Name (Get_Direct_Mapping_Id (F)));
                     raise Program_Error;
                  end if;
               end;
            end if;
         end loop;
      end if;

      --  Assume the dynamic invariant and frame condition of every variable in
      --  Loop_Writes if it was not discarded.

      for C in Loop_Writes.Iterate loop
         N := Key (C);

         if Element (C).Kind /= Discard then

            pragma Assert (Nkind (N) in N_Entity
                           and then Is_Object (N)
                           and then Is_Mutable_In_Why (N));

            declare
               Binder : constant Item_Type :=
                 Ada_Ent_To_Why.Element (Symbol_Table, N);
               Expr   : constant W_Expr_Id :=
                 Reconstruct_Item (Binder, Ref_Allowed => True);
               Status : Write_Status_Access := Element (C);

            begin
               Dyn_Types_Inv :=
                 +New_And_Expr
                 (Domain    => EW_Pred,
                  Conjuncts =>
                    (1 => +Dyn_Types_Inv,

                     --  Compute the dynamic property of Expr, taking into
                     --  account its initialization if it corresponds to a
                     --  variable taken as input in the current subprogram.

                     2 => +Compute_Dynamic_Invariant
                       (Expr        => +Expr,
                        Ty          => Etype (N),
                        Params      => Body_Params,
                        Initialized =>
                          (if not Is_Declared_In_Unit (N, Scope)
                             and then Is_Initialized (N, Scope)
                           then True_Term
                           else False_Term)),

                     --  Unmodified fields are preserved

                     3 => +Equality_Of_Preserved_Components
                       (Loop_Idx  => Loop_Index,
                        Is_Rev    => Is_Reverse,
                        Var_Known => Loop_Writes_Known (Loop_Id),
                        Loop_Vars => Modified,
                        Expr      => Expr,
                        At_Entry  => +Name_For_Loop_Entry
                          (Expr    => N,
                           Loop_Id => Loop_Id),
                        Expr_Ty   => Retysp (Etype (N)),
                        Status    => Status)));
            end;
         end if;
      end loop;

      return Dyn_Types_Inv;
   end Generate_Frame_Condition;

   ---------------------
   -- Get_Loop_Writes --
   ---------------------

   function Get_Loop_Writes
     (Loop_Stmt          : Node_Id;
      Has_Loop_Invariant : Boolean)
      return Write_Status_Maps.Map
   is
   begin
      --  Only try to keep variables declared inside the loop as completely
      --  written instead of discarded if there is a loop invariant (and this
      --  will only impact variables declared before the loop invariant).
      --  Otherwise, there is no meaningful use for these variables in the
      --  frame condition.

      return Loop_Writes : Write_Status_Maps.Map do
         Process_Loop_Statement (Loop_Stmt, Loop_Writes,
                                 Inv_Seen  => not Has_Loop_Invariant,
                                 In_Nested => False);
      end return;
   end Get_Loop_Writes;

   ----------------
   -- New_Status --
   ----------------

   function New_Status
     (New_Write      : Entity_Id;
      Discard_Writes : Boolean;
      Expected_Kind  : Write_Kind)
      return Write_Status_Access
   is
   begin
      --  If Discard_Writes is True, then discard the variable

      if Discard_Writes then

         return new Write_Status'(Kind => Discard);

      --  Otherwise, return a new status with the expected Write_Kind

      else
         case Expected_Kind is
            when Discard =>
               raise Program_Error;
            when Entire_Object =>
               return new Write_Status'(Kind => Entire_Object);
            when Record_Components =>
               if Retysp_Kind (Etype (New_Write)) in Record_Kind | Private_Kind
               then
                  return new
                    Write_Status'(Kind             => Record_Components,
                                  Component_Status => Empty_Map);
               else

                  --  We only handle separately parts of arrays and records.
                  --  Other objects can only be modified as a whole.

                  return new Write_Status'(Kind => Entire_Object);
               end if;
            when Array_Components =>
               return
               new Write_Status'(Kind              => Array_Components,
                                 Write_Constraints =>
                                    Array_Constraints_Maps.Empty_Map,
                                 Content_Status    => null);
         end case;
      end if;
   end New_Status;

   ----------------------
   -- One_Level_Update --
   ----------------------

   procedure One_Level_Update
     (New_Write      : Entity_Id;
      Loop_Writes    : in out Write_Status_Maps.Map;
      Discard_Writes : Boolean;
      Expected_Kind  : Write_Kind;
      Updated_Status : out Write_Status_Access)
   is
      Inserted : Boolean;
      C        : Cursor := Loop_Writes.Find (New_Write);

   begin
      if C = No_Element then

         --  New_Write does not exist in Loop_Writes; create it

         Loop_Writes.Insert
           (Key      => New_Write,
            New_Item => New_Status
              (New_Write, Discard_Writes => Discard_Writes,
               Expected_Kind => Expected_Kind),
            Inserted => Inserted,
            Position => C);

         pragma Assert (Inserted);

      elsif Discard_Writes then

         --  If Discard_Writes is set, New_Write's write status should stay
         --  as Discard.

         if Element (C).Kind /= Discard then

            --  If Discard_Writes is set, update New_Write's status to
            --  Discard if necessary.

            declare
               Old_Status : Write_Status_Access := Element (C);
            begin
               Finalize (Old_Status);
            end;

            Loop_Writes.Replace_Element
              (Position => C,
               New_Item => new Write_Status'(Kind => Discard));
         end if;

      elsif Expected_Kind = Entire_Object
        and then Element (C).Kind not in Entire_Object | Discard
      then

         --  If Expected_Kind is Entire_Object, update New_Write's status

         declare
            Old_Status : Write_Status_Access := Element (C);
         begin
            Finalize (Old_Status);
         end;

         Loop_Writes.Replace_Element
           (Position => C,
            New_Item => new Write_Status'(Kind => Entire_Object));

         --  Sanity check: the kind of a variable cannot change from
         --  Array_Elmt to Record_Components or reverse.

      elsif Expected_Kind /= Entire_Object
        and then Element (C).Kind not in Entire_Object | Discard
      then
         pragma Assert (Element (C).Kind = Expected_Kind);
      end if;

      Updated_Status := Element (C);
   end One_Level_Update;

   procedure One_Level_Update
     (New_Write      : Entity_Id;
      Loop_Writes    : in out Write_Status_Maps.Map;
      Discard_Writes : Boolean)
   is
      Updated_Status : Write_Status_Access;
   begin
      One_Level_Update
        (New_Write      => New_Write,
         Loop_Writes    => Loop_Writes,
         Expected_Kind  => Entire_Object,
         Discard_Writes => Discard_Writes,
         Updated_Status => Updated_Status);
   end One_Level_Update;

   ----------------------------
   -- Process_Call_Statement --
   ----------------------------

   procedure Process_Call_Statement
     (Call        : Node_Id;
      Loop_Writes : in out Write_Status_Maps.Map;
      Inv_Seen    : Boolean)
   is
      procedure Process_Param (Formal : Entity_Id; Actual : Node_Id);
      --  Update Loop_Writes with Actual if Formal is an out or an in out
      --  parameter.

      -------------------
      -- Process_Param --
      -------------------

      procedure Process_Param (Formal : Entity_Id; Actual : Node_Id) is
      begin
         if Ekind (Formal) in E_Out_Parameter | E_In_Out_Parameter then
            Update_Status (Actual, Loop_Writes, Inv_Seen);
         end if;
      end Process_Param;

      procedure Store_Parameters is new
        Iterate_Call_Parameters (Process_Param);

      Subp : constant Entity_Id := Get_Called_Entity (Call);

   --  Start of processing for Process_Call_Statement

   begin
      --  Record writes to out and in out parameters of the call

      Store_Parameters (Call);

      --  Record writes to the global out and in out of Subp

      declare
         Read_Ids  : Flow_Types.Flow_Id_Sets.Set;
         Write_Ids : Flow_Types.Flow_Id_Sets.Set;

      begin
         Flow_Utility.Get_Proof_Globals (Subprogram => Subp,
                                         Classwide  => True,
                                         Reads      => Read_Ids,
                                         Writes     => Write_Ids);

         for F of Write_Ids loop
            pragma Assert (F.Kind in Direct_Mapping | Magic_String);

            --  Magic_String are global state with no attached entities. As
            --  such state is translated as private in Why3, we do not need
            --  to assume any invariant for it.

            if F.Kind = Direct_Mapping then
               declare
                  Entity : constant Entity_Id := Get_Direct_Mapping_Id (F);
               begin
                  if Present (Entity)
                    and then Ekind (Entity) in Object_Kind
                    and then Is_Mutable_In_Why (Entity)
                  then
                     One_Level_Update (Entity, Loop_Writes,
                                       Discard_Writes => False);
                  end if;
               end;
            end if;
         end loop;
      end;

      --  Record write to the protected object for protected procedure or entry

      if Within_Protected_Type (Subp) then
         declare
            Call_Name   : constant Node_Id := Sinfo.Name (Call);
            Call_Prefix : Node_Id := Empty;

         begin
            --  Record the prefix for an external call

            if Nkind (Call_Name) = N_Selected_Component then
               Call_Prefix := Prefix (Call_Name);
            end if;

            --  External call, record the object itself

            if Present (Call_Prefix)
              and then not (Nkind (Call_Prefix) in N_Has_Entity
                              and then Is_Type (Entity (Call_Prefix)))
            then
               Update_Status (Call_Prefix, Loop_Writes, Inv_Seen);

            --  Internal call, we currently do not handle the implicit self
            --  reference.

            else
               null;
            end if;
         end;
      end if;
   end Process_Call_Statement;

   ----------------------------
   -- Process_Loop_Statement --
   ----------------------------

   procedure Process_Loop_Statement
     (Loop_Stmt   : Node_Id;
      Loop_Writes : in out Write_Status_Maps.Map;
      Inv_Seen    : Boolean;
      In_Nested   : Boolean)
   is
      Stmts  : constant List_Id := Statements (Loop_Stmt);
      Scheme : constant Node_Id := Iteration_Scheme (Loop_Stmt);

   begin
      --  The loop index is completely written

      if Present (Scheme)
        and then No (Condition (Scheme))
      then
         declare
            Loop_Param_Ent : Node_Id;
         begin
            if Present (Loop_Parameter_Specification (Scheme)) then
               Loop_Param_Ent := Defining_Identifier
                 (Loop_Parameter_Specification (Scheme));
            else
               pragma Assert (Present (Iterator_Specification (Scheme)));
               Loop_Param_Ent :=
                 Defining_Identifier (Iterator_Specification (Scheme));
            end if;

            --  For the loop index of the top-level loop, for which In_Nested
            --  is False, consider the variable as completely written instead
            --  of discarded, as this allows stating the dynamic property of
            --  the loop index in the frame condition.

            One_Level_Update (New_Write      => Loop_Param_Ent,
                              Loop_Writes    => Loop_Writes,
                              Discard_Writes => In_Nested or else Inv_Seen);
         end;
      end if;

      --  Process the statement list

      Process_Statement_List (Stmts, Loop_Writes, Inv_Seen, In_Nested);
   end Process_Loop_Statement;

   -----------------------
   -- Process_Statement --
   -----------------------

   procedure Process_Statement
     (N           : Node_Id;
      Loop_Writes : in out Write_Status_Maps.Map;
      Inv_Seen    : Boolean;
      In_Nested   : Boolean)
   is
   begin
      case Nkind (N) is
         when N_Assignment_Statement =>
            Update_Status (Sinfo.Name (N), Loop_Writes, Inv_Seen);

         --  Possibly record writes on variables local to the block (if
         --  In_Nested is still False at this point) as a Loop_Invariant
         --  is allowed to appear in a block.

         when N_Block_Statement =>
            declare
               Decls : constant List_Id := Declarations (N);
               HSS   : constant Node_Id := Handled_Statement_Sequence (N);
               --  Declarations, which are optional, and statement sequence,
               --  which is always present.

            begin
               if Present (Decls) then
                  Process_Statement_List
                    (Decls, Loop_Writes, Inv_Seen, In_Nested);
               end if;

               Process_Statement (HSS, Loop_Writes, Inv_Seen, In_Nested);
            end;

         --  Discard writes to variables local to a case statement

         when N_Case_Statement =>
            declare
               Alternative : Node_Id := First (Alternatives (N));
            begin
               while Present (Alternative) loop
                  Process_Statement_List
                    (Statements (Alternative), Loop_Writes, Inv_Seen,
                     In_Nested => True);
                  Next (Alternative);
               end loop;
            end;

         --  Discard writes to N if we are in a nested scope or if a loop
         --  invariant has already been encountered in the outer loop. The
         --  goal of passing In_Nested and Inv_Seen (starting from False) from
         --  the top-level call to Process_Loop_Statement through all calls
         --  traversing the tree is that we keep stating the dynamic property
         --  of local variables declared inside the loop before the loop
         --  invariant, for example:
         --
         --  loop
         --     declare
         --        X : T := ...
         --     begin
         --        pragma Loop_Invariant (...);
         --        declare
         --           Y : T := ...
         --        begin
         --           ...
         --        end;
         --     end;
         --  end loop;
         --
         --  As Inv_Seen is False when processing the declaration of X, the
         --  assignment to X is not discarded. Instead, X is marked as being
         --  completely written. As a result, the dynamic property of X is
         --  stated in the generated frame condition, which may be useful.
         --
         --  As Inv_Seen is True when processing the declaration of Y, the
         --  assignment to Y is discarded, and so Y is ignored in the generated
         --  frame condition. This is an optimisation, to avoid generating
         --  useless frame conditions, as Y cannot be mentioned in the frame
         --  condition in any meaningful way.

         when N_Object_Declaration =>
            declare
               E : constant Entity_Id := Defining_Identifier (N);
            begin
               if Is_Mutable_In_Why (E) then
                  One_Level_Update (E, Loop_Writes,
                                    Discard_Writes =>
                                      In_Nested or else Inv_Seen);
               end if;
            end;

         when N_Elsif_Part =>
            Process_Statement_List
              (Then_Statements (N), Loop_Writes, Inv_Seen, In_Nested => True);

         when N_Entry_Call_Statement
            | N_Procedure_Call_Statement
         =>
            Process_Call_Statement (N, Loop_Writes, Inv_Seen);

         --  Discard writes to variables local to a return statement

         when N_Extended_Return_Statement =>
            One_Level_Update (Return_Statement_Entity (N), Loop_Writes,
                              Discard_Writes => True);
            Process_Statement_List
              (Return_Object_Declarations (N), Loop_Writes, Inv_Seen,
               In_Nested => True);

            --  These statements do not affect the loop frame condition.
            --  We still include them here to match what flow analysis is
            --  doing in Get_Loop_Variables so that we can keep the check at
            --  the beginning of Generate_Frame_Condition.

            Process_Statement
              (Handled_Statement_Sequence (N), Loop_Writes, Inv_Seen,
               In_Nested => True);

         --  Discard writes to variables local to an if statement

         when N_If_Statement =>
            Process_Statement_List (Then_Statements (N), Loop_Writes,
                                    Inv_Seen, In_Nested => True);
            Process_Statement_List (Else_Statements (N), Loop_Writes,
                                    Inv_Seen, In_Nested => True);
            Process_Statement_List (Elsif_Parts (N), Loop_Writes,
                                    Inv_Seen, In_Nested => True);

         when N_Handled_Sequence_Of_Statements =>
            Process_Statement_List
              (Statements (N), Loop_Writes, Inv_Seen, In_Nested);

         --  Discard writes to variables local to a local loop statement

         when N_Loop_Statement =>
            Process_Loop_Statement
              (N, Loop_Writes, Inv_Seen, In_Nested => True);

         when N_Abstract_Subprogram_Declaration
            | N_Delay_Relative_Statement
            | N_Delay_Until_Statement
            | N_Exception_Declaration
            | N_Exception_Renaming_Declaration
            | N_Exit_Statement
            | N_Freeze_Entity
            | N_Freeze_Generic_Entity
            | N_Full_Type_Declaration
            | N_Generic_Instantiation
            | N_Generic_Package_Declaration
            | N_Generic_Renaming_Declaration
            | N_Generic_Subprogram_Declaration
            | N_Implicit_Label_Declaration
            | N_Incomplete_Type_Declaration
            | N_Itype_Reference
            | N_Label
            | N_Null_Statement
            | N_Number_Declaration
            | N_Object_Renaming_Declaration
            | N_Package_Body
            | N_Package_Body_Stub
            | N_Package_Declaration
            | N_Package_Renaming_Declaration
            | N_Pragma
            | N_Private_Extension_Declaration
            | N_Private_Type_Declaration
            | N_Protected_Body
            | N_Protected_Body_Stub
            | N_Protected_Type_Declaration
            | N_Raise_Statement
            | N_Raise_xxx_Error
            | N_Representation_Clause
            | N_Simple_Return_Statement
            | N_Subprogram_Body
            | N_Subprogram_Body_Stub
            | N_Subprogram_Declaration
            | N_Subprogram_Renaming_Declaration
            | N_Subtype_Declaration
            | N_Task_Body
            | N_Task_Body_Stub
            | N_Task_Type_Declaration
            | N_Use_Package_Clause
            | N_Use_Type_Clause
            | N_Validate_Unchecked_Conversion
         =>
            null;

         when others =>
            Ada.Text_IO.Put_Line ("[Loops.Inv.Process_Statement] kind ="
                                  & Node_Kind'Image (Nkind (N)));
            raise Program_Error;
      end case;
   end Process_Statement;

   ------------------------------
   --  Process_Statement_List  --
   ------------------------------

   procedure Process_Statement_List
     (L           : List_Id;
      Loop_Writes : in out Write_Status_Maps.Map;
      Inv_Seen    : Boolean;
      In_Nested   : Boolean)
   is
      N    : Node_Id := First (L);
      Seen : Boolean := Inv_Seen;

   begin
      while Present (N) loop

         --  If we are not in a nested loop, update Inv_Seen if the invariant
         --  is seen.

         if not In_Nested
           and then (Is_Pragma_Check (N, Name_Loop_Invariant)
                     or else Is_Pragma (N, Pragma_Loop_Variant))
         then
            Seen := True;
         end if;

         Process_Statement (N, Loop_Writes,
                            Inv_Seen  => Seen,
                            In_Nested => In_Nested);
         Next (N);
      end loop;
   end Process_Statement_List;

   -------------------
   -- Update_Status --
   -------------------

   procedure Update_Status
     (New_Write      : Node_Id;
      Loop_Writes    : in out Write_Status_Maps.Map;
      Inv_Seen       : Boolean;
      Expected_Kind  : Write_Kind;
      Expected_Type  : out Entity_Id;
      Updated_Status : out Write_Status_Access)
   is
   begin
      case Nkind (New_Write) is

         --  For identifiers, update the corresponding status. If New_Write has
         --  asynchronous writers, it is discarded so that none of its parts
         --  can be considered preserved.

         when N_Identifier
            | N_Expanded_Name
         =>
            One_Level_Update
              (New_Write      => Entity (New_Write),
               Loop_Writes    => Loop_Writes,
               Expected_Kind  => Expected_Kind,
               Discard_Writes => Has_Volatile (Entity (New_Write))
               or else Is_Protected_Component_Or_Discr_Or_Part_Of
                 (Entity (New_Write)),
               --  ??? protected components and Part_Of may only be accessed
               --  from within the protected operations where they appear
               --  as non-volatile (unless they are explicitly annotated
               --  as Volatile, if such an annotation is legal at all).
               --  ??? also, discriminants cannot be written, so this test
               --  seems too excessive anyway.
               Updated_Status => Updated_Status);

            Expected_Type := Retysp (Etype (New_Write));

         when N_Type_Conversion
            | N_Unchecked_Type_Conversion
         =>
            Update_Status (New_Write      => Expression (New_Write),
                           Loop_Writes    => Loop_Writes,
                           Inv_Seen       => Inv_Seen,
                           Expected_Kind  => Expected_Kind,
                           Expected_Type  => Expected_Type,
                           Updated_Status => Updated_Status);

         when N_Selected_Component =>

            --  Call Update_Status on Prefix (New_Write) with Expected_Kind set
            --  to Record_Components to create a status for it.

            Update_Status (New_Write      => Prefix (New_Write),
                           Loop_Writes    => Loop_Writes,
                           Inv_Seen       => Inv_Seen,
                           Expected_Kind  => Record_Components,
                           Expected_Type  => Expected_Type,
                           Updated_Status => Updated_Status);

            pragma Assert (Updated_Status.Kind in Entire_Object
                             | Discard | Record_Components);

            --  If Prefix (New_Write) is entirely written or if it is
            --  discarded, there is nothing to do.

            if Updated_Status.Kind = Record_Components then

               --  Get the corresponding field of the expected type so that
               --  the fields are found when we search for them during the
               --  construction of the frame condition.

               declare
                  Updated_Component  : constant Entity_Id :=
                    Entity (Selector_Name (New_Write));
                  Expected_Component : constant Entity_Id :=
                    Search_Component_By_Name (Expected_Type,
                                              Updated_Component);

               begin
                  --  If no corresponding field is found, the field must not be
                  --  visible in Expected_Type. This may occur if the entity is
                  --  downcasted before being assigned. Just discard it.

                  if No (Expected_Component) then
                     declare
                        Discarded_Component : constant Entity_Id :=
                          Original_Record_Component (Updated_Component);
                     begin
                        pragma Assert
                          (if Updated_Status.Component_Status.Contains
                             (Discarded_Component)
                           then
                             Updated_Status.Component_Status.Element
                               (Discarded_Component).Kind = Discard);

                        One_Level_Update
                          (New_Write      => Discarded_Component,
                           Loop_Writes    => Updated_Status.Component_Status,
                           Expected_Kind  => Expected_Kind,
                           Discard_Writes => True,
                           Updated_Status => Updated_Status);

                        --  This type should never be used.

                        Expected_Type := Empty;
                     end;

                  --  Otherwise update Expected_Component in Component_Status

                  else
                     One_Level_Update
                       (New_Write      => Expected_Component,
                        Loop_Writes    => Updated_Status.Component_Status,
                        Expected_Kind  => Expected_Kind,
                        Discard_Writes => False,
                        Updated_Status => Updated_Status);

                     Expected_Type := Retysp (Etype (Expected_Component));
                  end if;
               end;
            end if;

         when N_Indexed_Component
            | N_Slice
         =>
            --  Call Update_Status on Prefix (New_Write) with Expected_Kind set
            --  to Array_Components to create a status for it.

            Update_Status (New_Write      => Prefix (New_Write),
                           Loop_Writes    => Loop_Writes,
                           Inv_Seen       => Inv_Seen,
                           Expected_Kind  => Array_Components,
                           Expected_Type  => Expected_Type,
                           Updated_Status => Updated_Status);

            pragma Assert (Updated_Status.Kind in Entire_Object
                             | Discard | Array_Components);

            --  If Prefix (New_Write) is entirely written or if it is
            --  discarded, there is nothing to do.

            if Updated_Status.Kind = Array_Components then

               --  If Updated_Status.Content_Status is null, create a new
               --  status for it.

               if Updated_Status.Content_Status = null then
                  Updated_Status.Content_Status :=
                    New_Status
                      (New_Write, Discard_Writes => False,
                       Expected_Kind => Expected_Kind);

               --  If Expected_Kind is Entire_Object, update New_Write's status
               --  to Entire_Object if needed.

               elsif Expected_Kind = Entire_Object
                 and then not (Updated_Status.Content_Status.Kind in
                                 Entire_Object | Discard)
               then
                  declare
                     Old_Status : Write_Status_Access :=
                       Updated_Status.Content_Status;
                  begin
                     Finalize (Old_Status);
                  end;

                  Updated_Status.Content_Status :=
                    new Write_Status'(Kind => Entire_Object);

               --  Sanity check: the kind of a variable cannot change from
               --  Array_Elmt to Record_Components or reverse.

               elsif Expected_Kind /= Entire_Object
                 and then not (Updated_Status.Content_Status.Kind in
                                 Entire_Object | Discard)
               then
                  pragma Assert
                    (Updated_Status.Content_Status.Kind = Expected_Kind);
               end if;

               --  Store the new write in Updated_Status.Write_Constraints

               Updated_Status.Write_Constraints.Insert (New_Write, Inv_Seen);

               --  If we are updating a slice of an array, it is exactly as
               --  if we were updating the array as a whole.
               --  For indexed components, we are updating the component's
               --  status.

               if Nkind (New_Write) = N_Indexed_Component then
                  Updated_Status := Updated_Status.Content_Status;
                  Expected_Type := Retysp (Component_Type (Expected_Type));
               end if;
            end if;

         when others =>
            Ada.Text_IO.Put_Line ("[Update_Status] kind ="
                                  & Node_Kind'Image (Nkind (New_Write)));
            raise Program_Error;
      end case;
   end Update_Status;

   procedure Update_Status
     (New_Write   : Node_Id;
      Loop_Writes : in out Write_Status_Maps.Map;
      Inv_Seen    : Boolean)
   is
      Updated_Status : Write_Status_Access;
      Expected_Type  : Entity_Id;
   begin
      Update_Status
        (New_Write      => New_Write,
         Loop_Writes    => Loop_Writes,
         Inv_Seen       => Inv_Seen,
         Expected_Kind  => Entire_Object,
         Expected_Type  => Expected_Type,
         Updated_Status => Updated_Status);
   end Update_Status;

end Gnat2Why.Expr.Loops.Inv;
