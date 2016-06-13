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
with Sem_Util;               use Sem_Util;
with Snames;                 use Snames;
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
   --  status in Write_Status' additional field. We do not keep track of which
   --  array indexes are written.

   function Equality_Of_Preserved_Fields
     (Expr     : W_Expr_Id;
      At_Entry : W_Expr_Id;
      Expr_Ty  : Entity_Id;
      Status   : Write_Status_Access)
      return W_Pred_Id
     with Pre => Status /= null and then Status.Kind /= Discard;
   --  Compute a predicate which assumes preservation of every unmodified
   --  part of an expression.
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
       (Loop_Writes.Contains (New_Write)
        and then Loop_Writes.Element (New_Write).Kind = Discard =>
              Loop_Writes.Element (New_Write).Kind = Discard,
        Loop_Writes.Contains (New_Write)
        and then Loop_Writes.Element (New_Write).Kind = Entire_Object =>
              Loop_Writes.Element (New_Write).Kind in Discard | Entire_Object,
        others => True);

   procedure One_Level_Update
     (New_Write      : Entity_Id;
      Loop_Writes    : in out Write_Status_Maps.Map;
      Discard_Writes : Boolean);
   --  Same as before except that Expected_Kind is set to Entire_Object and
   --  Updated_Status is discarded.

   function New_Status
     (New_Write      : Entity_Id;
      Discard_Writes : Boolean;
      Expected_Kind  : Write_Kind)
      return Write_Status_Access
   with
     Pre  => Expected_Kind /= Discard;
   --  Create a Write_Status for New_Write.
   --  @param New_Write variable or record field to which we are writing.
   --  @param Expected_Kind expected kind of the updated status.
   --  @param Discard_Writes True if the writes to the variable should be
   --         discarded.
   --  @result an access to a fresh status for New_Write.

   --------------------
   -- Tree Traversal --
   --------------------

   function Get_Loop_Writes (Loop_Stmt : Node_Id) return Write_Status_Maps.Map;
   --  Traverse a loop statement and accumulate potentially written variables.
   --  @param Loop_Stmt considered loop statement.
   --  @return a map between written entities and their write status.

   procedure Process_Statement
     (N           : Node_Id;
      Loop_Writes : in out Write_Status_Maps.Map;
      Keep_Local  : Boolean);
   --  Traverse a statement and update a status map for every variable
   --  potentially written by the statement.
   --  @param N considered statement.
   --  @param Loop_Write a map between written entities and their write status.
   --  @param Keep_Local False if local variables should be discarded.

   procedure Process_Statement_List
     (L           : List_Id;
      Loop_Writes : in out Write_Status_Maps.Map;
      Keep_Local  : Boolean);
   --  Process every statement of a list.
   --  @param L considered list of statements.
   --  @param Loop_Write a map between written entities and their write status.
   --  @param Keep_Local False if local variables should be discarded.

   procedure Process_Call_Statement
     (Call        : Node_Id;
      Loop_Writes : in out Write_Status_Maps.Map);
   --  Update a status map for every variable written by a call statement.
   --  @param N considered statement.
   --  @param Loop_Write a map between written entities and their write status.

   procedure Process_Loop_Statement
     (Loop_Stmt   : Node_Id;
      Loop_Writes : in out Write_Status_Maps.Map;
      Keep_Local  : Boolean);
   --  Traverse a loop statement and update a status map for every variable
   --  potentially written by the loop.
   --  @param N considered statement.
   --  @param Loop_Write a map between written entities and their write status.
   --  @param Keep_Local False if local variables should be discarded.

   ----------------------------------
   -- Equality_Of_Preserved_Fields --
   ----------------------------------

   function Equality_Of_Preserved_Fields
     (Expr     : W_Expr_Id;
      At_Entry : W_Expr_Id;
      Expr_Ty  : Entity_Id;
      Status   : Write_Status_Access)
      return W_Pred_Id
   is
   begin
      case Status.Kind is
         when Discard =>
            raise Program_Error;
         when Entire_Object =>
            return True_Pred;
         when Record_Fields =>
            declare
               Field            : Entity_Id :=
                 First_Component_Or_Discriminant (Expr_Ty);
               Preserved_Fields : W_Pred_Id := True_Pred;
            begin
               while Present (Field) loop
                  if Component_Is_Visible_In_SPARK (Field)
                    and then (Ekind (Field) /= E_Discriminant
                              or else (Has_Defaulted_Discriminants (Expr_Ty)
                                       and then not Is_Constrained (Expr_Ty)))
                  then
                     declare
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
                        if Status.Field_Status.Contains (Field) then

                           --  Field is modified. Look for its preserved fields

                           Inv := Equality_Of_Preserved_Fields
                             (Expr     => F_Expr,
                              At_Entry => F_At_Entry,
                              Expr_Ty  => F_Expr_Ty,
                              Status   => Status.Field_Status.Element (Field));

                           --  Remove visited fields for sanity checking.

                           declare
                              Old_Status : Write_Status_Access :=
                                Status.Field_Status.Element (Field);
                           begin
                              Finalize (Old_Status);
                           end;

                           Status.Field_Status.Exclude (Field);
                        else

                           --  Field is preserved

                           Inv := +New_Comparison (Symbol => Why_Eq,
                                                   Left   => F_Expr,
                                                   Right  => F_At_Entry,
                                                   Domain => EW_Pred);
                        end if;
                        Preserved_Fields :=
                          +New_And_Expr (Left   => +Preserved_Fields,
                                         Right  => +Inv,
                                         Domain => EW_Pred);
                     end;
                  end if;

                  Field := Next_Component_Or_Discriminant (Field);
               end loop;

               --  Sanity checking: all the non-visited fields are discarded.

               pragma Assert (for all E of Status.Field_Status =>
                                E.Kind = Discard);

               return Preserved_Fields;
            end;
         when Array_Elmts =>

            --  Generates:
            --  forall i1 .. in : int. in_range i1 /\ .. /\ in_range in ->
            --    Equality_Of_Preserved_Fields (get <Expr> i1 .. in)

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
                       New_Range_Expr
                         (Domain => EW_Pred,
                          Low    => Insert_Conversion_To_Rep_No_Bool
                            (EW_Term,
                             Get_Array_Attr (Domain => EW_Term,
                                             Expr   => +Expr,
                                             Attr   => Attribute_First,
                                             Dim    => I)),
                          High   => Insert_Conversion_To_Rep_No_Bool
                            (EW_Term,
                             Get_Array_Attr (Domain => EW_Term,
                                             Expr   => +Expr,
                                             Attr   => Attribute_Last,
                                             Dim    => I)),
                          Expr   => +Tmp),
                     Domain => EW_Pred);
                  Next_Index (Index);
                  I := I + 1;
               end loop;

               pragma Assert (I = Indices'Last + 1);

               declare
                  E_Expr_Ty  : constant Entity_Id :=
                    Retysp (Component_Type (Expr_Ty));
                  E_Expr     : constant W_Expr_Id :=
                    New_Array_Access (Empty, Expr, Indices, EW_Term);
                  E_At_Entry : constant W_Expr_Id :=
                    New_Array_Access (Empty, At_Entry, Indices, EW_Term);
                  Preserved_Fields : W_Expr_Id :=
                    +Equality_Of_Preserved_Fields
                      (Expr     => E_Expr,
                       At_Entry => E_At_Entry,
                       Expr_Ty  => E_Expr_Ty,
                       Status   => Status.Elmt_Status);
               begin
                  if +Preserved_Fields /= True_Pred then
                     Preserved_Fields := New_Conditional
                       (Domain    => EW_Pred,
                        Condition => +Range_Expr,
                        Then_Part => Preserved_Fields,
                        Typ       => EW_Bool_Type);

                     return New_Universal_Quantif
                       (Binders => Vars,
                        Pred    => +Preserved_Fields);
                  else
                     return True_Pred;
                  end if;
               end;
            end;
      end case;
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
         when Entire_Object | Discard =>
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

   function Generate_Frame_Condition (Loop_Stmt : Node_Id) return W_Pred_Id is
      Loop_Writes   : constant Map := Get_Loop_Writes (Loop_Stmt);
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
                  --  be modified from a proof point of view.

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
                          (Full_Name (Get_Direct_Mapping_Id (F)));
                        pragma Assert (False);
                     end if;
                  end;
               end if;
            end loop;
         end;
      end if;

      --  Assume the dynamic invariant of every variable in Loop_Writes if
      --  it was nor discarded.

      for C in Loop_Writes.Iterate loop
         N := Key (C);

         pragma Assert (Nkind (N) in N_Entity
                        and then Ekind (N) in Object_Kind
                        and then Is_Mutable_In_Why (N));

         if Element (C).Kind /= Discard then
            declare
               Binder   : constant Item_Type :=
                 Ada_Ent_To_Why.Element (Symbol_Table, N);
               Expr     : constant W_Expr_Id :=
                 Reconstruct_Item (Binder, Ref_Allowed => True);
            begin

               --  Compute the dynamic property of Expr

               Dyn_Types_Inv :=
                 +New_And_Expr
                 (Domain    => EW_Pred,
                  Conjuncts =>
                    (1 => +Dyn_Types_Inv,
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
                        Status   => Element (C))));
            end;
         end if;

         --  We don't need N's status anymore; finalize it to free the memory

         declare
            Status : Write_Status_Access := Element (C);
         begin
            Finalize (Status);
         end;
      end loop;

      return Dyn_Types_Inv;
   end Generate_Frame_Condition;

   ---------------------
   -- Get_Loop_Writes --
   ---------------------

   function Get_Loop_Writes (Loop_Stmt : Node_Id) return Write_Status_Maps.Map
   is
   begin
      return Loop_Writes : Write_Status_Maps.Map do
         Process_Loop_Statement (Loop_Stmt, Loop_Writes, Keep_Local => True);
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
        and then not (Element (C).Kind in Entire_Object | Discard)
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
        and then not (Element (C).Kind in Entire_Object | Discard)
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
         Read_Ids    : Flow_Types.Flow_Id_Sets.Set;
         Write_Ids   : Flow_Types.Flow_Id_Sets.Set;

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

         --  External call, record the object itself

         declare
            Call_Name : constant Node_Id := Sinfo.Name (Call);
         begin

            if Nkind (Call_Name) = N_Selected_Component
              and then
                not (Nkind (Prefix (Call_Name)) in N_Has_Entity
                     and then Is_Type (Entity (Prefix (Call_Name))))
            then
               pragma Assert
                 (Has_Async_Writers
                    (Direct_Mapping_Id (Entity (Prefix (Call_Name)))));
               Update_Status (Prefix (Call_Name), Loop_Writes);

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

         when N_Block_Statement =>

            --  Record writes on variables local to the block as a
            --  Loop_Invariant is allowed to appear in a block.

            declare
               Decls : constant List_Id := Declarations (N);
               HSS   : constant Node_Id := Handled_Statement_Sequence (N);
            begin
               if Present (Decls) then
                  Process_Statement_List (Decls, Loop_Writes, Keep_Local);
               end if;

               pragma Assert (Present (HSS));

               if Present (HSS) then
                  Process_Statement (HSS, Loop_Writes, Keep_Local);
               end if;
            end;

         when N_Case_Statement =>

            --  Discard writes to variables local to a case statement

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

         when N_Object_Declaration =>

            --  Discard writes to N if we are not interested in local objects

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
              (Then_Statements (N), Loop_Writes, Keep_Local);

         when N_Entry_Call_Statement     |
              N_Procedure_Call_Statement =>
            Process_Call_Statement (N, Loop_Writes);

         when N_Extended_Return_Statement =>

            --  Discard writes to variables local to a return statement

            One_Level_Update (Return_Statement_Entity (N), Loop_Writes,
                              Discard_Writes => True);
            Process_Statement_List
              (Return_Object_Declarations (N), Loop_Writes,
               Keep_Local => False);

         when N_If_Statement =>

            --  Discard writes to variables local to an if statement

            Process_Statement_List (Then_Statements (N), Loop_Writes,
                                    Keep_Local => False);
            Process_Statement_List (Else_Statements (N), Loop_Writes,
                                    Keep_Local => False);
            Process_Statement_List (Elsif_Parts (N), Loop_Writes,
                                    Keep_Local => False);

         when N_Handled_Sequence_Of_Statements =>
            Process_Statement_List (Statements (N), Loop_Writes, Keep_Local);

         when N_Loop_Statement =>

            --  Discard writes to variables local to a loop statement

            Process_Loop_Statement (N, Loop_Writes, Keep_Local => False);

         when N_Abstract_Subprogram_Declaration |
              N_Delay_Relative_Statement        |
              N_Delay_Until_Statement           |
              N_Exception_Declaration           |
              N_Exception_Renaming_Declaration  |
              N_Exit_Statement                  |
              N_Freeze_Entity                   |
              N_Freeze_Generic_Entity           |
              N_Full_Type_Declaration           |
              N_Generic_Instantiation           |
              N_Generic_Package_Declaration     |
              N_Generic_Renaming_Declaration    |
              N_Generic_Subprogram_Declaration  |
              N_Implicit_Label_Declaration      |
              N_Incomplete_Type_Declaration     |
              N_Itype_Reference                 |
              N_Label                           |
              N_Null_Statement                  |
              N_Number_Declaration              |
              N_Object_Renaming_Declaration     |
              N_Package_Body                    |
              N_Package_Body_Stub               |
              N_Package_Declaration             |
              N_Package_Renaming_Declaration    |
              N_Pragma                          |
              N_Private_Extension_Declaration   |
              N_Private_Type_Declaration        |
              N_Protected_Body                  |
              N_Protected_Body_Stub             |
              N_Protected_Type_Declaration      |
              N_Raise_Statement                 |
              N_Raise_xxx_Error                 |
              N_Representation_Clause           |
              N_Simple_Return_Statement         |
              N_Subprogram_Body                 |
              N_Subprogram_Body_Stub            |
              N_Subprogram_Declaration          |
              N_Subprogram_Renaming_Declaration |
              N_Subtype_Declaration             |
              N_Task_Body                       |
              N_Task_Body_Stub                  |
              N_Task_Type_Declaration           |
              N_Use_Package_Clause              |
              N_Use_Type_Clause                 |
              N_Validate_Unchecked_Conversion =>
            null;

         when others =>
            Ada.Text_IO.Put_Line ("[Loops.Inv.Process_Statement] kind ="
                                  & Node_Kind'Image (Nkind (N)));
            raise Why.Not_Implemented;

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
      N : Node_Id := First (L);

   begin
      while Present (N) loop
         Process_Statement (N, Loop_Writes, Keep_Local);
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
         when N_Identifier | N_Expanded_Name =>

            --  Update the corresponding status. If New_Write has asynchronous
            --  writers, it is discarded so that known of its parts can be
            --  considered preserved.

            One_Level_Update
              (New_Write      => Entity (New_Write),
               Loop_Writes    => Loop_Writes,
               Expected_Kind  => Expected_Kind,
               Discard_Writes => Has_Async_Writers
                 (Direct_Mapping_Id (Entity (New_Write))),
               Updated_Status => Updated_Status);

            Expected_Type := Retysp (Etype (New_Write));

         when N_Type_Conversion | N_Unchecked_Type_Conversion =>

            Update_Status (New_Write      => Expression (New_Write),
                           Loop_Writes    => Loop_Writes,
                           Expected_Kind  => Expected_Kind,
                           Expected_Type  => Expected_Type,
                           Updated_Status => Updated_Status);

         when N_Selected_Component =>

            --  Call Update_Status on Prefix (New_Item) with Expected_Kind set
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

               --  Get the corresponding field of the expected type so that the
               --  fields are found when we search for them during the
               --  construction of the frame condition.

               declare
                  Updated_Field  : constant Entity_Id :=
                    Entity (Selector_Name (New_Write));
                  Expected_Field : constant Entity_Id :=
                    Search_Component_By_Name (Expected_Type, Updated_Field);
               begin
                  if No (Expected_Field) then

                     --  No corresponding field is found. The field must not be
                     --  visible in Expected_Type. Just discard it.

                     pragma Assert
                       (Has_Private_Ancestor_Or_Root (Expected_Type));

                     declare
                        Discarded_Field : constant Entity_Id :=
                          Original_Record_Component (Updated_Field);
                     begin

                        pragma Assert
                          (if Updated_Status.Field_Status.Contains
                             (Discarded_Field) then
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
                  else

                     --  Update Expected_Field in Field_Status.

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

         when N_Indexed_Component | N_Slice =>

            --  Call Update_Status on Prefix (New_Item) with Expected_Kind set
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

               --  If Updated_Status.Elmt_Status, create a new status for it

               if Updated_Status.Elmt_Status = null then
                  Updated_Status.Elmt_Status :=
                    New_Status
                      (New_Write, Discard_Writes => False,
                       Expected_Kind => Expected_Kind);

               elsif Expected_Kind = Entire_Object
                 and then not (Updated_Status.Elmt_Status.Kind in
                                 Entire_Object | Discard)
               then

                  --  If Expected_Kind is Entire_Object, update New_Write's
                  --  status to Entire_Object.

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
            raise Not_Implemented;
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
