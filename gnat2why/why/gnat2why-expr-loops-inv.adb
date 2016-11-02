------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--               G N A T 2 W H Y - E X P R - L O O P S - I N V              --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2016, AdaCore                        --
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
with Sem_Aux;                use Sem_Aux;
with Sem_Util;               use Sem_Util;
with Snames;                 use Snames;
with SPARK_Util.Subprograms; use SPARK_Util.Subprograms;
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

   type Write_Kind is (Entire_Object, Record_Fields, Array_Elmts, Discard);
   --  The status of a variable or a part of a variable.
   --   * Entire_Object the object is entirely written.
   --   * Record_Fields some fields (maybe all) of the record object are
   --                   written.
   --   * Array_Elmts   some indexes (maybe all) of the array object are
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

   type Write_Status (Kind : Write_Kind) is limited record
      case Kind is
         when Entire_Object | Discard => null;
         when Record_Fields =>
            Field_Status : Write_Status_Maps.Map;
         when Array_Elmts   =>
            Elmt_Status  : Write_Status_Access;
      end case;
   end record;
   --  If only some parts of the object are written, we store their write
   --  status in Write_Status additional fields. We do not keep track of
   --  which array indexes are written.

   function Equality_Of_Preserved_Fields
     (Expr     : W_Expr_Id;
      At_Entry : W_Expr_Id;
      Expr_Ty  : Entity_Id;
      Status   : in out Write_Status_Access)
      return W_Pred_Id
   with
     Pre => Status /= null and then Status.Kind /= Discard;
   --  Compute a predicate which assumes preservation of every unmodified
   --  part of an expression. Status is finalized by the call for sanity
   --  checking purpose.
   --  @param Expr Why expression at the current loop index.
   --  @param At_Entry Why expression at the loop's entry.
   --  @param Expr_Ty Ada type of Expr.
   --  @param Status Write_Status of Expr.
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
   --  @param Expected_Kind expected kind of the updated status.
   --  @param Expected_Type type of the actual updated object part.
   --  @param Updated_Status access to New_Write's write status.

   procedure Update_Status
     (New_Write   : Node_Id;
      Loop_Writes : in out Write_Status_Maps.Map);
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
      Loop_Writes : in out Write_Status_Maps.Map);
   --  Update a status map for every variable written by a call statement.
   --  @param Call considered call statement.
   --  @param Loop_Writes a map between written entities and their write
   --         status.

   procedure Process_Loop_Statement
     (Loop_Stmt   : Node_Id;
      Loop_Writes : in out Write_Status_Maps.Map;
      Keep_Local  : Boolean);
   --  Traverse a loop statement and update a status map for every variable
   --  potentially written by the loop.
   --  @param Loop_Stmt considered loop statement.
   --  @param Loop_Writes a map between written entities and their write
   --         status.
   --  @param Keep_Local False if local variables should be discarded.

   procedure Process_Statement
     (N           : Node_Id;
      Loop_Writes : in out Write_Status_Maps.Map;
      Keep_Local  : Boolean);
   --  Traverse a statement and update a status map for every variable
   --  potentially written by the statement.
   --  @param N considered statement.
   --  @param Loop_Writes a map between written entities and their write
   --         status.
   --  @param Keep_Local False if local variables should be discarded.

   procedure Process_Statement_List
     (L           : List_Id;
      Loop_Writes : in out Write_Status_Maps.Map;
      Keep_Local  : Boolean);
   --  Process every statement of a list.
   --  @param L considered list of statements.
   --  @param Loop_Writes a map between written entities and their write
   --         status.
   --  @param Keep_Local False if local variables should be discarded.

   ----------------------------------
   -- Equality_Of_Preserved_Fields --
   ----------------------------------

   function Equality_Of_Preserved_Fields
     (Expr     : W_Expr_Id;
      At_Entry : W_Expr_Id;
      Expr_Ty  : Entity_Id;
      Status   : in out Write_Status_Access)
      return W_Pred_Id
   is
      Preserved_Fields : W_Pred_Id := True_Pred;

      procedure Handle_Field (Field : Entity_Id);
      --  Generate the appropriate equality if the field is preserved and calls
      --  Equality_Of_Preserved_Fields recursively otherwise.

      procedure Handle_Field (Field : Entity_Id) is
         F_Expr_Ty  : constant Entity_Id :=
           Retysp (Etype (Field));
         F_Expr     : constant W_Expr_Id :=
           New_Ada_Record_Access (Ada_Node => Empty,
                                  Name     => Expr,
                                  Domain   => EW_Term,
                                  Field    => Field,
                                  Ty       => Expr_Ty);
         F_At_Entry : constant W_Expr_Id :=
           New_Ada_Record_Access (Ada_Node => Empty,
                                  Name     => At_Entry,
                                  Domain   => EW_Term,
                                  Field    => Field,
                                  Ty       => Expr_Ty);
         Inv        : W_Pred_Id;

      begin
         --  Field is modified

         if Status.Field_Status.Contains (Field) then

            declare
               F_Status : Write_Status_Access :=
                 Status.Field_Status.Element (Field);
            begin

               --  Look for its preserved subfields

               Inv := Equality_Of_Preserved_Fields
                 (Expr     => F_Expr,
                  At_Entry => F_At_Entry,
                  Expr_Ty  => F_Expr_Ty,
                  Status   => F_Status);
            end;

            --  Remove visited fields for sanity checking

            Status.Field_Status.Exclude (Field);

            --  Field is preserved

         else
            Inv := +New_Comparison (Symbol => Why_Eq,
                                    Left   => F_Expr,
                                    Right  => F_At_Entry,
                                    Domain => EW_Pred);
         end if;

         Preserved_Fields :=
           +New_And_Expr (Left   => +Preserved_Fields,
                          Right  => +Inv,
                          Domain => EW_Pred);
      end Handle_Field;

   begin
      case Status.Kind is
         when Discard =>
            raise Program_Error;

         when Entire_Object =>
            Preserved_Fields := True_Pred;

         when Record_Fields =>

            --  Only consider fields which are mutable, hence not discriminants
            --  of types without default discriminants or of constrained types.

            if Has_Discriminants (Expr_Ty)
              and then Has_Defaulted_Discriminants (Expr_Ty)
              and then not Is_Constrained (Expr_Ty)
            then
               declare
                  Discr : Entity_Id := First_Discriminant (Expr_Ty);
               begin

                  while Present (Discr) loop

                     if not Is_Completely_Hidden (Discr) then
                        Handle_Field (Discr);
                     end if;

                     Discr := Next_Discriminant (Discr);
                  end loop;
               end;
            end if;

            for Field of Get_Component_Set (Expr_Ty) loop

               --  Only consider fields which are visible in Expr_Ty.

               if Component_Is_Visible_In_Type (Expr_Ty, Field) then
                  Handle_Field (Field);
               end if;
            end loop;

            --  Sanity checking: all the non-visited fields are discarded

            pragma Assert (for all E of Status.Field_Status =>
                             E.Kind = Discard);

         --  For arrays, generate:
         --  forall i1 .. in : int. in_range i1 /\ .. /\ in_range in ->
         --    Equality_Of_Preserved_Fields (get <Expr> i1 .. in)

         when Array_Elmts =>
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
                  E_Expr_Ty   : constant Entity_Id :=
                    Retysp (Component_Type (Expr_Ty));
                  E_Expr      : constant W_Expr_Id :=
                    New_Array_Access (Empty, Expr, Indices, EW_Term);
                  E_At_Entry  : constant W_Expr_Id :=
                    New_Array_Access (Empty, At_Entry, Indices, EW_Term);
                  Elmt_Fields : W_Expr_Id :=
                    +Equality_Of_Preserved_Fields
                      (Expr     => E_Expr,
                       At_Entry => E_At_Entry,
                       Expr_Ty  => E_Expr_Ty,
                       Status   => Status.Elmt_Status);
               begin
                  if +Elmt_Fields /= True_Pred then
                     Elmt_Fields := New_Conditional
                       (Domain    => EW_Pred,
                        Condition => +Range_Expr,
                        Then_Part => Elmt_Fields,
                        Typ       => EW_Bool_Type);

                     Preserved_Fields := New_Universal_Quantif
                       (Binders => Vars,
                        Pred    => +Elmt_Fields);
                  end if;
               end;
            end;
      end case;
      Finalize (Status);
      return Preserved_Fields;
   end Equality_Of_Preserved_Fields;

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
         when Record_Fields =>
            for E of Status.Field_Status loop
               Finalize (E);
            end loop;
         when Array_Elmts   =>
            Finalize (Status.Elmt_Status);
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
      Scope         : constant Entity_Id := Enclosing_Unit (Loop_Id);
      N             : Node_Id;
      Dyn_Types_Inv : W_Pred_Id := True_Pred;

   begin
      --  Sanity checking:
      --  Check that we have at least every variable modified in the loop.

      if Loop_Writes_Known (Loop_Id) then
         declare
            Modified : constant Flow_Id_Sets.Set :=
              To_Entire_Variables (Flow_Utility.Get_Loop_Writes (Loop_Id));
         begin
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
                       and then Ekind (E) in Object_Kind
                       and then Is_Mutable_In_Why (E)
                       and then not Has_Async_Writers (F)
                       and then
                         (not Is_Task_Type (Etype (E))
                          or else Has_Discriminants (Etype (E)))
                     then
                        Ada.Text_IO.Put_Line
                          ("error in computation of loop frame condition for "
                           & Full_Name (Get_Direct_Mapping_Id (F)));
                        raise Program_Error;
                     end if;
                  end;
               end if;
            end loop;
         end;
      end if;

      --  Assume the dynamic invariant of every variable in Loop_Writes if
      --  it was not discarded.

      for C in Loop_Writes.Iterate loop
         N := Key (C);

         if Element (C).Kind /= Discard then

            pragma Assert (Nkind (N) in N_Entity
                           and then Ekind (N) in Object_Kind
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
                        Initialized =>
                          (if not Is_Declared_In_Unit (N, Scope)
                             and then Is_Initialized (N, Scope)
                           then True_Term
                           else False_Term)),

                     --  Unmodified fields are preserved

                     3 => +Equality_Of_Preserved_Fields
                       (Expr     => Expr,
                        At_Entry => +Name_For_Loop_Entry
                          (Expr    => N,
                           Loop_Id => Loop_Id),
                        Expr_Ty  => Retysp (Etype (N)),
                        Status   => Status)));
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
                                 Keep_Local => Has_Loop_Invariant);
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
            when Record_Fields =>
               if Retysp_Kind (Etype (New_Write)) in Record_Kind | Private_Kind
               then
                  return new Write_Status'(Kind         => Record_Fields,
                                           Field_Status => Empty_Map);
               else

                  --  We only handle separately parts of arrays and records.
                  --  Other objects can only be modified as a whole.

                  return new Write_Status'(Kind => Entire_Object);
               end if;
            when Array_Elmts =>
               return new Write_Status'(Kind        => Array_Elmts,
                                        Elmt_Status => null);
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
         --  Array_Elmt to Record_Fields or reverse.

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
      Loop_Writes : in out Write_Status_Maps.Map)
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
            Update_Status (Actual, Loop_Writes);
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

      if Is_Protected_Subprogram (Subp) then
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
               pragma Assert
                 (Has_Async_Writers
                    (Direct_Mapping_Id (Entity (Call_Prefix))));
               Update_Status (Call_Prefix, Loop_Writes);

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
      Keep_Local  : Boolean)
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

            --  For the loop index of the top-level loop, for which Keep_Local
            --  is True, consider the variable as completely written instead of
            --  discarded, as this allows stating the dynamic property of the
            --  loop index in the frame condition.

            One_Level_Update (New_Write      => Loop_Param_Ent,
                              Loop_Writes    => Loop_Writes,
                              Discard_Writes => not Keep_Local);
         end;
      end if;

      --  Process the statement list

      Process_Statement_List (Stmts, Loop_Writes, Keep_Local);
   end Process_Loop_Statement;

   -----------------------
   -- Process_Statement --
   -----------------------

   procedure Process_Statement
     (N           : Node_Id;
      Loop_Writes : in out Write_Status_Maps.Map;
      Keep_Local  : Boolean)
   is
   begin
      case Nkind (N) is
         when N_Assignment_Statement =>
            Update_Status (Sinfo.Name (N), Loop_Writes);

         --  Possibly record writes on variables local to the block (if
         --  Keep_Local is still True at this point) as a Loop_Invariant
         --  is allowed to appear in a block.

         when N_Block_Statement =>
            declare
               Decls : constant List_Id := Declarations (N);
               HSS   : constant Node_Id := Handled_Statement_Sequence (N);
               --  Declarations, which are optional, and statement sequence,
               --  which is always present.

            begin
               if Present (Decls) then
                  Process_Statement_List (Decls, Loop_Writes, Keep_Local);
               end if;

               Process_Statement (HSS, Loop_Writes, Keep_Local);
            end;

         --  Discard writes to variables local to a case statement

         when N_Case_Statement =>
            declare
               Alternative : Node_Id := First (Alternatives (N));
            begin
               while Present (Alternative) loop
                  Process_Statement_List
                    (Statements (Alternative), Loop_Writes,
                     Keep_Local => False);
                  Next (Alternative);
               end loop;
            end;

         --  Discard writes to N if we are not interested in local objects.
         --  The goal of passing Keep_Local (starting from value True) from
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
         --  As Keep_Local is True when processing the declaration of X, the
         --  assignment to X is not discarded. Instead, X is marked as being
         --  completely written. As a result, the dynamic property of X is
         --  stated in the generated frame condition, which may be useful.
         --
         --  As Keep_Local is False when processing the declaration of Y, the
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
                                    Discard_Writes => not Keep_Local);
               end if;
            end;

         when N_Elsif_Part =>
            Process_Statement_List
              (Then_Statements (N), Loop_Writes, Keep_Local => False);

         when N_Entry_Call_Statement
            | N_Procedure_Call_Statement
         =>
            Process_Call_Statement (N, Loop_Writes);

         --  Discard writes to variables local to a return statement

         when N_Extended_Return_Statement =>
            One_Level_Update (Return_Statement_Entity (N), Loop_Writes,
                              Discard_Writes => True);
            Process_Statement_List
              (Return_Object_Declarations (N), Loop_Writes,
               Keep_Local => False);

         --  Discard writes to variables local to an if statement

         when N_If_Statement =>
            Process_Statement_List (Then_Statements (N), Loop_Writes,
                                    Keep_Local => False);
            Process_Statement_List (Else_Statements (N), Loop_Writes,
                                    Keep_Local => False);
            Process_Statement_List (Elsif_Parts (N), Loop_Writes,
                                    Keep_Local => False);

         when N_Handled_Sequence_Of_Statements =>
            Process_Statement_List (Statements (N), Loop_Writes, Keep_Local);

         --  Discard writes to variables local to a local loop statement

         when N_Loop_Statement =>
            Process_Loop_Statement (N, Loop_Writes, Keep_Local => False);

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
      Keep_Local  : Boolean)
   is
      N    : Node_Id := First (L);
      Keep : Boolean := Keep_Local;

   begin
      while Present (N) loop

         --  No need to keep variables declared after the loop invariant,
         --  as there is no meaningful use of these variables in the frame
         --  condition.

         if Is_Pragma_Check (N, Name_Loop_Invariant) then
            Keep := False;
         end if;

         Process_Statement (N, Loop_Writes, Keep);
         Next (N);
      end loop;
   end Process_Statement_List;

   -------------------
   -- Update_Status --
   -------------------

   procedure Update_Status
     (New_Write      : Node_Id;
      Loop_Writes    : in out Write_Status_Maps.Map;
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
                           Expected_Kind  => Expected_Kind,
                           Expected_Type  => Expected_Type,
                           Updated_Status => Updated_Status);

         when N_Selected_Component =>

            --  Call Update_Status on Prefix (New_Write) with Expected_Kind set
            --  to Record_Fields to create a status for it.

            Update_Status (New_Write      => Prefix (New_Write),
                           Loop_Writes    => Loop_Writes,
                           Expected_Kind  => Record_Fields,
                           Expected_Type  => Expected_Type,
                           Updated_Status => Updated_Status);

            pragma Assert (Updated_Status.Kind in Entire_Object
                             | Discard | Record_Fields);

            --  If Prefix (New_Write) is entirely written or if it is
            --  discarded, there is nothing to do.

            if Updated_Status.Kind = Record_Fields then

               --  Get the corresponding field of the expected type so that
               --  the fields are found when we search for them during the
               --  construction of the frame condition.

               declare
                  Updated_Field  : constant Entity_Id :=
                    Entity (Selector_Name (New_Write));
                  Expected_Field : constant Entity_Id :=
                    Search_Component_By_Name (Expected_Type, Updated_Field);

               begin
                  --  If no corresponding field is found, the field must not be
                  --  visible in Expected_Type. This may occur if the entity is
                  --  downcasted before being assigned. Just discard it.

                  if No (Expected_Field) then
                     declare
                        Discarded_Field : constant Entity_Id :=
                          Original_Record_Component (Updated_Field);
                     begin
                        pragma Assert
                          (if Updated_Status.Field_Status.Contains
                             (Discarded_Field)
                           then
                             Updated_Status.Field_Status.Element
                               (Discarded_Field).Kind = Discard);

                        One_Level_Update
                          (New_Write      => Discarded_Field,
                           Loop_Writes    => Updated_Status.Field_Status,
                           Expected_Kind  => Expected_Kind,
                           Discard_Writes => True,
                           Updated_Status => Updated_Status);

                        --  This type should never be used.

                        Expected_Type := Empty;
                     end;

                  --  Otherwise update Expected_Field in Field_Status

                  else
                     One_Level_Update
                       (New_Write      => Expected_Field,
                        Loop_Writes    => Updated_Status.Field_Status,
                        Expected_Kind  => Expected_Kind,
                        Discard_Writes => False,
                        Updated_Status => Updated_Status);

                     Expected_Type := Retysp (Etype (Expected_Field));
                  end if;
               end;
            end if;

         when N_Indexed_Component
            | N_Slice
         =>
            --  Call Update_Status on Prefix (New_Write) with Expected_Kind set
            --  to Array_Elmts to create a status for it.

            Update_Status (New_Write      => Prefix (New_Write),
                           Loop_Writes    => Loop_Writes,
                           Expected_Kind  => Array_Elmts,
                           Expected_Type  => Expected_Type,
                           Updated_Status => Updated_Status);

            pragma Assert (Updated_Status.Kind in Entire_Object
                             | Discard | Array_Elmts);

            --  If Prefix (New_Write) is entirely written or if it is
            --  discarded, there is nothing to do.

            if Updated_Status.Kind = Array_Elmts then

               --  If Updated_Status.Elmt_Status is null, create a new status
               --  for it.

               if Updated_Status.Elmt_Status = null then
                  Updated_Status.Elmt_Status :=
                    New_Status
                      (New_Write, Discard_Writes => False,
                       Expected_Kind => Expected_Kind);

               --  If Expected_Kind is Entire_Object, update New_Write's status
               --  to Entire_Object if needed.

               elsif Expected_Kind = Entire_Object
                 and then not (Updated_Status.Elmt_Status.Kind in
                                 Entire_Object | Discard)
               then
                  declare
                     Old_Status : Write_Status_Access :=
                       Updated_Status.Elmt_Status;
                  begin
                     Finalize (Old_Status);
                  end;

                  Updated_Status.Elmt_Status :=
                    new Write_Status'(Kind => Entire_Object);

               --  Sanity check: the kind of a variable cannot change from
               --  Array_Elmt to Record_Fields or reverse.

               elsif Expected_Kind /= Entire_Object
                 and then not (Updated_Status.Elmt_Status.Kind in
                                 Entire_Object | Discard)
               then
                  pragma Assert
                    (Updated_Status.Elmt_Status.Kind = Expected_Kind);
               end if;

               --  If we are updating a slice of an array, it is exactly as
               --  if we were updating the array as a whole.
               --  For indexed components, we are updating the component's
               --  status.

               if Nkind (New_Write) = N_Indexed_Component then
                  Updated_Status := Updated_Status.Elmt_Status;
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
      Loop_Writes : in out Write_Status_Maps.Map)
   is
      Updated_Status : Write_Status_Access;
      Expected_Type  : Entity_Id;
   begin
      Update_Status
        (New_Write      => New_Write,
         Loop_Writes    => Loop_Writes,
         Expected_Kind  => Entire_Object,
         Expected_Type  => Expected_Type,
         Updated_Status => Updated_Status);
   end Update_Status;

end Gnat2Why.Expr.Loops.Inv;
