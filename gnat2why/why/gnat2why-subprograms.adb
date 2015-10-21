------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - S U B P R O G R A M S                --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2015, AdaCore                   --
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

with Common_Containers;      use Common_Containers;
with Errout;                 use Errout;
with Flow_Dependency_Maps;   use Flow_Dependency_Maps;
with Flow_Generated_Globals; use Flow_Generated_Globals;
with Flow_Refinement;        use Flow_Refinement;
with Flow_Types;             use Flow_Types;
with Flow_Utility;           use Flow_Utility;
with GNAT.Source_Info;
with Gnat2Why.Expr;          use Gnat2Why.Expr;
with Namet;                  use Namet;
with Nlists;                 use Nlists;
with Sem_Aux;                use Sem_Aux;
with Sem_Disp;               use Sem_Disp;
with Sem_Util;               use Sem_Util;
with Sinfo;                  use Sinfo;
with Sinput;                 use Sinput;
with Snames;                 use Snames;
with SPARK_Definition;       use SPARK_Definition;
with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;
with SPARK_Util;             use SPARK_Util;
with Stand;                  use Stand;
with System;                 use System;
with Uintp;                  use Uintp;
with VC_Kinds;               use VC_Kinds;
with Why;                    use Why;
with Why.Atree.Accessors;    use Why.Atree.Accessors;
with Why.Atree.Builders;     use Why.Atree.Builders;
with Why.Atree.Modules;      use Why.Atree.Modules;
with Why.Atree.Mutators;     use Why.Atree.Mutators;
with Why.Conversions;        use Why.Conversions;
with Why.Gen.Consts;         use Why.Gen.Consts;
with Why.Gen.Decl;           use Why.Gen.Decl;
with Why.Gen.Expr;           use Why.Gen.Expr;
with Why.Gen.Names;          use Why.Gen.Names;
with Why.Gen.Preds;          use Why.Gen.Preds;
with Why.Gen.Progs;          use Why.Gen.Progs;
with Why.Gen.Terms;          use Why.Gen.Terms;
with Why.Inter;              use Why.Inter;
with Why.Types;              use Why.Types;

package body Gnat2Why.Subprograms is

   -----------------------
   -- Local Subprograms --
   -----------------------

   function Compute_Args
     (E       : Entity_Id;
      Binders : Binder_Array) return W_Expr_Array;
   --  Given a function entity, and an array of logical binders,
   --  compute a call of the logical Why function corresponding to E.
   --  In general, the binder array has *more* arguments than the Ada entity,
   --  because of effects. Note that these effect variables are not bound here,
   --  they refer to the global variables

   procedure Compute_Contract_Cases_Guard_Map
     (E                  : Entity_Id;
      Guard_Map          : out Ada_To_Why_Ident.Map;
      Others_Guard_Ident : out W_Identifier_Id;
      Others_Guard_Expr  : out W_Expr_Id);
   --  Returns the map from contracts cases nodes attached to subprogram E,
   --  if any, to Why identifiers for the value of these guards in the Why3
   --  program. If the contract cases contain an "others" case, return in
   --  Others_Guard_Ident an identifier for a Boolean value set to true when
   --  this case is enabled, and in Others_Guard_Expr the Why3 expression
   --  to define this identifier. If there is no "others" case, return with
   --  Others_Guard_Ident set to Why_Empty.

   function Compute_Contract_Cases_Entry_Checks
     (E         : Entity_Id;
      Guard_Map : Ada_To_Why_Ident.Map) return W_Prog_Id;
   --  Returns the Why program for checking that the guards of the
   --  Contract_Cases pragma attached to subprogram E (if any) are disjoint,
   --  and that they cover all cases prescribed by the precondition. The checks
   --  that evaluating guards do not raise run-time errors are done separately,
   --  based on the result of Compute_Contract_Cases_Guard_Map. Guard_Map
   --  stores a mapping from guard AST nodes to temporary Why names, so that
   --  the caller can compute the Why expression for these in the pre-state,
   --  and bind them appropriately.

   function Compute_Contract_Cases_Exit_Checks
     (Params             : Transformation_Params;
      E                  : Entity_Id;
      Guard_Map          : Ada_To_Why_Ident.Map;
      Others_Guard_Ident : W_Identifier_Id) return W_Prog_Id;
   --  Returns in Result the Why program for checking that the consequence of
   --  enabled guard of the Contract_Cases pragma attached to subprogram E (if
   --  any) does not raise a run-time error, and that it holds. Guard_Map
   --  stores a mapping from guard AST nodes to temporary Why names, so that
   --  the caller can compute the Why expression for these in the pre-state,
   --  and bind them appropriately.

   function Compute_Contract_Cases_Postcondition
     (Params : Transformation_Params;
      E      : Entity_Id) return W_Pred_Id;
   --  Returns the postcondition corresponding to the Contract_Cases pragma for
   --  subprogram E (if any), to be used in the postcondition of the program
   --  function.

   function Compute_Dynamic_Property_For_Inputs
     (E              : Entity_Id;
      Params         : Transformation_Params;
      Pred_Fun_Param : Entity_Id := Empty;
      Initialized    : Boolean := False) return W_Prog_Id
   with
       Pre => Ekind (E) in
         E_Procedure | E_Function | E_Package | E_Task_Type | E_Entry;
   --  Given a Why node, collects the set of external dynamic objects
   --  that are referenced in this node.
   --  @param E Entity of subprogram or task or entry or package.
   --  @param Pred_Fun_Param not Empty iff computing the dynamic property for
   --     inputs of a predicate function, in which case [Pred_Fun_Param] is
   --     the entity for the formal parameter of the predicate function.
   --  @param Initialized Assume global out to be initialized at this point.
   --  @result an assumption including the dynamic property of every external
   --     dynamic objects that are referenced in W.

   function Compute_Dynamic_Property_For_Effects
     (E      : Entity_Id;
      Params : Transformation_Params) return W_Pred_Id;
   --  Returns an assumption including the dynamic property of every object
   --  modified by a subprogram.

   function Compute_Effects
     (E             : Entity_Id;
      Global_Params : Boolean := False) return W_Effects_Id;
   --  Compute the effects of the generated Why function. If Global_Params is
   --  True, then the global version of the parameters is used.

   function Compute_Binders (E : Entity_Id; Domain : EW_Domain)
                             return Item_Array;
   --  Return Why binders for the parameters of subprogram E.
   --  If Domain is EW_Term also generates binders for E's read effects.
   --  The array is a singleton of unit type if the array is empty.

   function Add_Logic_Binders (E           : Entity_Id;
                               Raw_Binders : Item_Array) return Item_Array;
   --  Return Why binders for the parameters and read effects of function E.
   --  The array is a singleton of unit type if E has no parameters and no
   --  effects.

   procedure Assume_Value_Of_Constants
     (Why_Expr : in out W_Prog_Id;
      Scope    : Entity_Id;
      Params   : Transformation_Params);
   --  Go through Why_Expr to find all the Ada node referencing constants with
   --  no variable input to assume their definition.
   --  ??? This is especially needed for record aggregates containing floating
   --      point numbers and should not be needed anymore once floating point
   --      numbers are properly handled by solvers.

   function Compute_Raw_Binders (E : Entity_Id) return Item_Array;
   --  Return Why binders for the parameters of subprogram E. The array is
   --  empty if E has no parameters.

   function Compute_Guard_Formula (Binders : Item_Array) return W_Pred_Id;
   --  For every scalar object in the binder array, build the formula
   --    in_range (x)
   --  and join everything together with a conjunction.

   function Get_Location_For_Aspect
     (E         : Entity_Id;
      Kind      : Name_Id;
      Classwide : Boolean := False) return Node_Id;
   --  Return a node with a proper location for the pre- or postcondition of E,
   --  if any.

   procedure Generate_Subprogram_Program_Fun
     (File : Why_Section;
      E    : Entity_Id);
   --  Generate a why program function for E

   procedure Generate_Axiom_For_Post
     (File : Why_Section;
      E    : Entity_Id);
   --  Generate an axiom stating the postcondition of a Subprogram

   function Check_Ceiling_Protocol
     (Params : Transformation_Params;
      E      : Entity_Id) return W_Prog_Id
     with Pre => Is_Task_Type (E);
   --  @param Params the transformation params
   --  @param E a task type entity
   --  @return an assertion or sequence of assertion that expresses that the
   --    ceiling protocol is respected in the call graph starting from this
   --    task, i.e. basically that external calls to protected operations are
   --    made with a priority lower or equal to the priority of the object in
   --    question.

   ----------------------------------
   -- Add_Dependencies_For_Effects --
   ----------------------------------

   procedure Add_Dependencies_For_Effects
     (T : W_Theory_Declaration_Id;
      E : Entity_Id)
   is
      Read_Ids    : Flow_Types.Flow_Id_Sets.Set;
      Write_Ids   : Flow_Types.Flow_Id_Sets.Set;
      Read_Names  : Name_Sets.Set;
      Write_Names : Name_Sets.Set;
   begin
      --  Collect global variables potentially read and written

      Flow_Utility.Get_Proof_Globals (Subprogram => E,
                                      Classwide  => True,
                                      Reads      => Read_Ids,
                                      Writes     => Write_Ids);
      Read_Names  := Flow_Types.To_Name_Set (Read_Ids);
      Write_Names := Flow_Types.To_Name_Set (Write_Ids);

      Add_Effect_Imports (T, Read_Names);
      Add_Effect_Imports (T, Write_Names);

   end Add_Dependencies_For_Effects;

   -------------------------------
   -- Assume_Value_Of_Constants --
   -------------------------------

   procedure Assume_Value_Of_Constants
     (Why_Expr : in out W_Prog_Id;
      Scope    : Entity_Id;
      Params   : Transformation_Params)
   is
      Include : constant Node_Sets.Set := Compute_Ada_Node_Set (+Why_Expr);
      Assumes : W_Prog_Id := New_Void;
   begin
      for N of Include loop
         if Present (N)
           and then Nkind (N) in N_Entity
           and then Ekind (N) = E_Constant
           and then not Has_Variable_Input (Direct_Mapping_Id (N))
           and then not Is_Declared_In_Unit (N, Scope)
         then
            Assume_Declaration_Of_Entity
              (E             => N,
               Params        => Params,
               Initialized   => True,
               Top_Predicate => True,
               Context       => Assumes);
         end if;
      end loop;
      Why_Expr := Sequence (Assumes, Why_Expr);
   end Assume_Value_Of_Constants;

   ----------------------------
   -- Check_Ceiling_Protocol --
   ----------------------------

   function Check_Ceiling_Protocol
     (Params : Transformation_Params;
      E      : Entity_Id) return W_Prog_Id is

      function Check_Local_Call (Ent : Entity_Name; Prio : W_Expr_Id)
                                 return W_Prog_Id;
      --  @param E the entity of the calling object/task
      --  @param Prio the active priority of the task used for all the calls
      --  @return one or several assertions checking violations of the ceiling
      --    protocol

      ----------------------
      -- Check_Local_Call --
      ----------------------

      function Check_Local_Call (Ent : Entity_Name; Prio : W_Expr_Id)
                                 return W_Prog_Id
      is
         S : W_Prog_Id := New_Void;
      begin
         if Prio = Why_Empty then
            return
              New_Located_Assert (Ada_Node => E,
                                  Pred     => False_Pred,
                                  Reason   => VC_Ceiling_Priority_Protocol,
                                  Kind     => EW_Check);
         end if;

         --  Both the current priority and object priority are present

         for Name of Directly_Called_Tasking_Objects (Ent) loop

            --  Skip regular calls

            if not Is_Protected_Subprogram (Find_Entity (Name)) then
               return Check_Local_Call (Name, Prio);
            end if;

            --  We are computing the ceiling priority of the object here. See
            --  ARM Annex D.3, 7-11, with the extra twist that we assume the
            --  ceiling priority to be Interrupt_Priority'Last even in the
            --  presence of Attach_Handler (so we basically ignore rule 10/3).

            declare
               Ada_Obj_Prio : constant Node_Id :=
                 Get_Priority_Or_Interrupt_Priority
                   (Containing_Protected_Type (Find_Entity (Name)));
               Obj_Prio : constant W_Expr_Id :=
                 (if Present (Ada_Obj_Prio) then
                       Transform_Expr
                         (Ada_Obj_Prio, EW_Int_Type, EW_Pterm, Params)
                  else
                    +New_Constant
                    (UI_From_Int (Int (Interrupt_Priority'Last))));
                     Pred     : constant W_Pred_Id :=
                       +New_Comparison (Symbol => Int_Infix_Le,
                                        Left   => Prio,
                                        Right  => Obj_Prio,
                                        Domain => EW_Pred);
                     Check    : constant W_Prog_Id :=
                       New_Located_Assert (Ada_Node => E,
                                           Pred     => Pred,
                                           Reason   =>
                                             VC_Ceiling_Priority_Protocol,
                                           Kind     => EW_Check);
            begin
               S :=
                 Sequence ((1 => S,
                            2 => Check,
                            3 => Check_Local_Call (Name, Obj_Prio)));
            end;
         end loop;
         return S;
      end Check_Local_Call;

      --  Start of processing for Check_Ceiling_Protocol

      Task_Prio : constant Node_Id :=
        Get_Priority_Or_Interrupt_Priority (E);
      Why_Prio : constant W_Expr_Id :=
        (if Present (Task_Prio) then
              Transform_Expr (Task_Prio, EW_Int_Type, EW_Pterm, Params)
         else
            +New_Constant (UI_From_Int (Int (Interrupt_Priority'Last))));
   begin
      return Check_Local_Call (To_Entity_Name (E), Why_Prio);
   end Check_Ceiling_Protocol;

   ------------------
   -- Compute_Args --
   ------------------

   function Compute_Args
     (E       : Entity_Id;
      Binders : Binder_Array) return W_Expr_Array
   is
      Cnt    : Integer := 1;
      Result : W_Expr_Array (1 .. Binders'Last);
      Ada_Binders : constant List_Id :=
        Parameter_Specifications (Subprogram_Specification (E));
      Arg_Length  : Nat := List_Length (Ada_Binders);

   begin

      if Is_Protected_Subprogram (E) then
         Arg_Length := Arg_Length + 1;
      end if;

      if Arg_Length = 0
        and then not Flow_Utility.Has_Proof_Global_Reads (E, Classwide => True)
      then
         return W_Expr_Array'(1 => New_Void);
      end if;

      while Cnt <= Integer (Arg_Length) loop
         Result (Cnt) := +Binders (Cnt).B_Name;
         Cnt := Cnt + 1;
      end loop;

      while Cnt <= Binders'Last loop
         Result (Cnt) := Get_Logic_Arg (Binders (Cnt), True);
         Cnt := Cnt + 1;
      end loop;

      return Result;
   end Compute_Args;

   ---------------------
   -- Compute_Binders --
   ---------------------

   function Compute_Binders (E : Entity_Id; Domain : EW_Domain)
                             return Item_Array is
      Binders     : constant Item_Array :=
        Compute_Subprogram_Parameters  (E, Domain);
   begin

         --  If E has no parameters, return a singleton of unit type.

         if Binders'Length = 0 then
            return (1 => (Regular, Unit_Param));
         else
            return Binders;
         end if;
   end Compute_Binders;

   -----------------------------------------
   -- Compute_Dynamic_Property_For_Inputs --
   -----------------------------------------

   function Compute_Dynamic_Property_For_Inputs
     (E              : Entity_Id;
      Params         : Transformation_Params;
      Pred_Fun_Param : Entity_Id := Empty;
      Initialized    : Boolean := False) return W_Prog_Id
   is
      Read_Ids   : Flow_Types.Flow_Id_Sets.Set;

      function Is_Initialized (Obj : Entity_Id) return Boolean with
        Pre => not Is_Declared_In_Unit (Obj, E)
        and then Is_Mutable_In_Why (Obj);
      --  Returns True if Obj is always initialized in the scope of E.

      function Is_Initialized (Obj : Entity_Id) return Boolean is
      begin
         if not Initialized
           and then Ekind (E) in E_Function | E_Procedure
         then

            --  Inside a subprogram, global variables may be uninitialized if
            --  they do not occur as reads of the subprogram.

            return (Enclosing_Package_Or_Subprogram (Obj) = E
                    and then Ekind (Obj) /= E_Out_Parameter)
              or else Read_Ids.Contains (Direct_Mapping_Id (Obj));
         else

            --  Every global variable referenced inside a package elaboration
            --  must be initialized.

            return True;
         end if;
      end Is_Initialized;

      Includes            : Node_Sets.Set;
      Dynamic_Prop_Inputs : W_Prog_Id := New_Void;

   begin
      --  Collect global variables read or written in E

      if Ekind (E) in E_Function | E_Procedure | E_Task_Type then
         declare
            Write_Ids   : Flow_Types.Flow_Id_Sets.Set;
            Read_Names  : Name_Sets.Set;
            Write_Names : Name_Sets.Set;
         begin

            --  Also get references to global constants with variable inputs
            --  even if they are constants in Why.

            Flow_Utility.Get_Proof_Globals (Subprogram     => E,
                                            Classwide      => True,
                                            Reads          => Read_Ids,
                                            Writes         => Write_Ids,
                                            Keep_Constants => True);

            Read_Names  := Flow_Types.To_Name_Set (Read_Ids);
            Write_Names := Flow_Types.To_Name_Set (Write_Ids);

            for R of Read_Names loop
               declare
                  Entity : constant Entity_Id := Find_Entity (R);
               begin
                  if Present (Entity) then
                     Includes.Insert (Entity);
                  end if;
               end;
            end loop;

            for R of Write_Names loop
               declare
                  Entity : constant Entity_Id := Find_Entity (R);
               begin
                  if Present (Entity) then
                     Includes.Include (Entity);
                  end if;
               end;
            end loop;
         end;
      elsif Ekind (E) = E_Package and then not Is_Wrapper_Package (E) then

         --  For packages, we use the Initializes aspect to get the variables
         --  referenced during elaboration.
         --  We don't do it for wrapper packages as Initializes are not
         --  generated for them.

         declare
            Init_Map : constant Dependency_Maps.Map :=
              Parse_Initializes (Get_Pragma (E, Pragma_Initializes),
                                 E,
                                 Get_Flow_Scope (E));
         begin
            for S of Init_Map loop
               for Y of S loop

                  --  Expand Abstract_State if any.

                  declare
                     Reads  : constant Flow_Id_Sets.Set :=
                       Expand_Abstract_State (Y, Erase_Constants => False);
                     Entity : Entity_Id;
                  begin

                     --  Get the entity associated with the Flow_Ids.

                     for X of Reads loop
                        case X.Kind is
                        when Direct_Mapping | Record_Field =>
                           Entity := Find_Entity (To_Entity_Name (X.Node));
                        when Magic_String =>
                           Entity := Find_Entity (X.Name);
                        when Null_Value | Synthetic_Null_Export =>
                           raise Program_Error;
                        end case;

                        if Present (Entity) then
                           Includes.Include (Entity);
                        end if;
                     end loop;
                  end;
               end loop;
            end loop;
         end;
      end if;

      --  Collect parameters of E if any
      --  ??? We may want to account for discriminants of task types and self
      --  reference of protected subprograms.

      if Ekind (E) in E_Function | E_Procedure then
         declare
            Params : constant List_Id :=
              (if Is_Entry (E) then Parameter_Specifications (Parent (E))
               else Parameter_Specifications (Subprogram_Specification (E)));
            Param  : Node_Id;
         begin
            Param := First (Params);
            while Present (Param) loop
               Includes.Include (Defining_Identifier (Param));
               Next (Param);
            end loop;
         end;
      end if;

      declare
         Already_Included : Node_Sets.Set := Node_Sets.Empty_Set;
         Prop_For_Include : W_Prog_Id;
         Top_Predicate    : Boolean;
         Variables        : Flow_Id_Sets.Set;
         --  Set of variable inputs used in the assumed dynamic invariants.
         --  We will also need to assume their dynamic invariant.

      begin
         while not Node_Sets.Is_Empty (Includes) loop
            Prop_For_Include := New_Void;
            Flow_Id_Sets.Clear (Variables);
            for Obj of Includes loop

               --  No need to assume anything if Obj is not an object, if it is
               --  not in SPARK or if it is a local object of the unit.

               if not (Nkind (Obj) in N_Entity)
                 or else not (Is_Object (Obj) or else Is_Named_Number (Obj))
                 or else not Entity_In_SPARK (Obj)
                 or else not Ada_Ent_To_Why.Has_Element (Symbol_Table, Obj)
                 or else Is_Declared_In_Unit (Obj, E)
               then
                  null;
               else
                  --  If Obj is the parameter of a predicate function, do not
                  --  assume the toplevel predicate for checking absence of RTE
                  --  in the predicate function itself.

                  Top_Predicate := Obj /= Pred_Fun_Param;

                  Assume_Declaration_Of_Entity
                    (E             => Obj,
                     Params        => Params,
                     Initialized   =>
                       (if Is_Object (Obj) and then Is_Mutable_In_Why (Obj)
                        then Is_Initialized (Obj)
                        else True),
                     Top_Predicate => Top_Predicate,
                     Context       => Prop_For_Include);

                  --  Add all the variable inputs of the dynamic invariant
                  --  to the set of variables to consider.

                  Variables_In_Dynamic_Invariant (Etype (Obj), Variables);
               end if;
            end loop;

            Dynamic_Prop_Inputs := Sequence
              (Prop_For_Include, Dynamic_Prop_Inputs);
            Node_Sets.Union (Already_Included, Includes);
            Includes := Compute_Ada_Node_Set (+Prop_For_Include);

            --  Add the variable inputs of dynamic predicates to Includes so
            --  that their dynamic invariant can be assumed.

            for Name of To_Name_Set (Variables) loop
               Node_Sets.Include (Includes, Find_Entity (Name));
            end loop;

            Node_Sets.Difference (Includes, Already_Included);
         end loop;
      end;

      return Dynamic_Prop_Inputs;
   end Compute_Dynamic_Property_For_Inputs;

   function Compute_Dynamic_Property_For_Effects
     (E      : Entity_Id;
      Params : Transformation_Params) return W_Pred_Id
   is
      Func_Why_Binders     : constant Binder_Array :=
        To_Binder_Array (Compute_Binders (E, EW_Prog));
      Dynamic_Prop_Effects : W_Pred_Id := True_Pred;
   begin

      --  Compute the dynamic property of mutable parameters

      for I in Func_Why_Binders'Range loop
         if Func_Why_Binders (I).Mutable then
            declare
               Binder   : constant Binder_Type := Func_Why_Binders (I);
               Dyn_Prop : constant W_Pred_Id :=
                 Compute_Dynamic_Invariant
                   (Expr => +Transform_Identifier (Params => Params,
                                                   Expr   => Binder.Ada_Node,
                                                   Ent    => Binder.Ada_Node,
                                                   Domain => EW_Term),
                    Ty   => Etype (Binder.Ada_Node));
            begin
               Dynamic_Prop_Effects := +New_And_Expr
                 (Left   => +Dynamic_Prop_Effects,
                  Right  => +Dyn_Prop,
                  Domain => EW_Pred);
            end;
         end if;
      end loop;

      --  Compute the dynamic property of global output

      declare
         Read_Ids    : Flow_Types.Flow_Id_Sets.Set;
         Write_Ids   : Flow_Types.Flow_Id_Sets.Set;
         Write_Names : Name_Sets.Set;
      begin
         Flow_Utility.Get_Proof_Globals (Subprogram => E,
                                         Classwide  => True,
                                         Reads      => Read_Ids,
                                         Writes     => Write_Ids);
         Write_Names := Flow_Types.To_Name_Set (Write_Ids);

         for Name of Write_Names loop
            declare
               Entity : constant Entity_Id := Find_Entity (Name);
            begin
               if Present (Entity)
                 and then not (Ekind (Entity) = E_Abstract_State)
                 and then Entity_In_SPARK (Entity)
               then

                  --  ??? skip dynamic invariant for protected type

                  if Ekind (Entity) in Type_Kind then
                     pragma Assert (Ekind (Entity) in Protected_Kind);
                     null;
                  else
                     declare
                        Dyn_Prop : constant W_Pred_Id :=
                          Compute_Dynamic_Invariant
                            (Expr =>
                               +Transform_Identifier (Params   => Params,
                                                      Expr     => Entity,
                                                      Ent      => Entity,
                                                      Domain   => EW_Term),
                             Ty   => Etype (Entity));
                     begin
                        Dynamic_Prop_Effects := +New_And_Expr
                          (Left   => +Dynamic_Prop_Effects,
                           Right  => +Dyn_Prop,
                           Domain => EW_Pred);
                     end;
                  end if;
               end if;
            end;
         end loop;
      end;

      return Dynamic_Prop_Effects;
   end Compute_Dynamic_Property_For_Effects;

   ---------------------
   -- Compute_Effects --
   ---------------------

   function Compute_Effects
     (E             : Entity_Id;
      Global_Params : Boolean := False) return W_Effects_Id
   is
      Read_Ids    : Flow_Types.Flow_Id_Sets.Set;
      Write_Ids   : Flow_Types.Flow_Id_Sets.Set;
      Read_Names  : Name_Sets.Set;
      Write_Names : Name_Sets.Set;
      Eff         : constant W_Effects_Id := New_Effects;

      generic
         with procedure Effects_Append
           (Id : W_Effects_Id; New_Item : W_Identifier_Id);
      procedure Effects_Append_Binder (Binder : Item_Type);
      --  Append to effects Eff the variable associated with an item
      --  @param Binder variable to add to Eff

      ---------------------------
      -- Effects_Append_Binder --
      ---------------------------

      procedure Effects_Append_Binder (Binder : Item_Type)  is
      begin
         case Binder.Kind is
            when Regular | Prot_Self =>
               if Binder.Main.Mutable then
                  Effects_Append (Eff, Binder.Main.B_Name);
               end if;
            when UCArray =>
               Effects_Append (Eff, Binder.Content.B_Name);
            when DRecord =>
               if Binder.Fields.Present then
                  Effects_Append (Eff, Binder.Fields.Binder.B_Name);
               end if;
               if Binder.Discrs.Present
                 and then Binder.Discrs.Binder.Mutable
               then
                  Effects_Append (Eff, Binder.Discrs.Binder.B_Name);
               end if;
            when Func    => raise Program_Error;
         end case;
      end Effects_Append_Binder;

      procedure Effects_Append_Binder_To_Reads is
         new Effects_Append_Binder (Effects_Append_To_Reads);

      procedure Effects_Append_Binder_To_Writes is
         new Effects_Append_Binder (Effects_Append_To_Writes);

   begin
      --  Collect global variables potentially read and written

      Flow_Utility.Get_Proof_Globals (Subprogram => E,
                                      Classwide  => True,
                                      Reads      => Read_Ids,
                                      Writes     => Write_Ids);
      Read_Names  := Flow_Types.To_Name_Set (Read_Ids);
      Write_Names := Flow_Types.To_Name_Set (Write_Ids);

      for Name of Write_Names loop
         declare
            Entity : constant Entity_Id := Find_Entity (Name);
         begin

            if Present (Entity)
              and then not (Ekind (Entity) = E_Abstract_State)
              and then Entity_In_SPARK (Entity)
            then

               --  Take into account special case of effect on protected
               --  components

               if Ekind (Entity) in Type_Kind then
                  pragma Assert (Ekind (Entity) in Protected_Kind);
                  declare
                     Binder : constant Item_Type :=
                       Item_Type'(Kind => Prot_Self,
                                  Main => Protected_Self_Binder (Entity));
                  begin
                     Effects_Append_Binder_To_Writes (Binder);
                  end;
               else
                  declare
                     Binder : constant Item_Type :=
                       Ada_Ent_To_Why.Element (Symbol_Table, Entity);
                  begin
                     Effects_Append_Binder_To_Writes (Binder);
                  end;
               end if;
            else
               Effects_Append_To_Writes
                 (Eff,
                  To_Why_Id (Obj => To_String (Name), Local => False));
            end if;
         end;
      end loop;

      --  Add all OUT and IN OUT parameters as potential writes
      --  If Global_Params is True, use binders from the Symbol_Table.
      --  Otherwise, use binders from the function declaration.

      if Global_Params then
         declare
            Params : constant List_Id :=
              Parameter_Specifications (Subprogram_Specification (E));
            Param  : Node_Id;
         begin
            Param := First (Params);
            while Present (Param) loop
               declare
                  B  : constant Item_Type :=
                    Ada_Ent_To_Why.Element
                      (Symbol_Table, Defining_Entity (Param));
               begin
                  Effects_Append_Binder_To_Writes (B);
               end;
               Next (Param);
            end loop;
         end;
      else
         declare
            Binders : constant Item_Array := Compute_Raw_Binders (E);
         begin
            for B of Binders loop
               Effects_Append_Binder_To_Writes (B);
            end loop;
         end;
      end if;

      for Name of Read_Names loop
         declare
            Entity : constant Entity_Id := Find_Entity (Name);
         begin

            if Present (Entity)
              and then not (Ekind (Entity) = E_Abstract_State)
              and then Entity_In_SPARK (Entity)
            then

               --  Take into account special case of effect on protected
               --  components

               if Ekind (Entity) in Type_Kind then
                  pragma Assert (Ekind (Entity) in Protected_Kind);
                  declare
                     Binder : constant Item_Type :=
                       Item_Type'(Kind => Prot_Self,
                                  Main => Protected_Self_Binder (Entity));
                  begin
                     Effects_Append_Binder_To_Reads (Binder);
                  end;
               else
                  declare
                     Binder : constant Item_Type :=
                       Ada_Ent_To_Why.Element (Symbol_Table, Entity);
                  begin
                     Effects_Append_Binder_To_Reads (Binder);
                  end;
               end if;
            else
               Effects_Append_To_Reads
                 (Eff,
                  To_Why_Id (Obj => To_String (Name), Local => False));
            end if;
         end;
      end loop;

      return +Eff;
   end Compute_Effects;

   ---------------------------
   -- Compute_Guard_Formula --
   ---------------------------

   function Compute_Guard_Formula (Binders : Item_Array) return W_Pred_Id
   is
      Pred : W_Pred_Id := True_Pred;
   begin
      for B of Binders loop
         if B.Kind = Regular and then
           Present (B.Main.Ada_Node) and then
           Use_Why_Base_Type (B.Main.Ada_Node)
         then

            --  The Ada_Node contains the Ada entity for the parameter

            declare
               Ty    : constant Entity_Id :=
                 Unique_Entity (Etype (B.Main.Ada_Node));
               Guard : constant W_Pred_Id :=
                 (if Type_Is_Modeled_As_Base (Etype (B.Main.Ada_Node)) then
                  +New_Dynamic_Property (Domain => EW_Pred,
                                         Ty     => Ty,
                                         Expr   => +B.Main.B_Name)
                  else New_Call (Name => E_Symb (Ty, WNE_Range_Pred),
                                 Args => (1 => +B.Main.B_Name)));
            begin
               Pred :=
                 +New_And_Then_Expr
                 (Domain => EW_Pred,
                  Left   => +Pred,
                  Right  => +Guard);
            end;
         else

            --  Add to guard the dynamic property of logic parameters.

            declare
               Ada_Node : constant Node_Id :=
                 Get_Ada_Node_From_Item (B);
               Expr     : constant W_Expr_Id :=
                 Reconstruct_Item (B, True);
               Ty_Node  : constant Entity_Id :=
                 (if Present (Ada_Node) then
                      (if Is_Type (Ada_Node) then Ada_Node
                       else Etype (Ada_Node))
                  else Empty);
               Dyn_Prop : constant W_Pred_Id :=
                 (if Present (Ty_Node) then
                    Compute_Dynamic_Invariant (Expr => +Expr,
                                               Ty   => Ty_Node)
                  else
                    True_Pred);
            begin
               if No (Ada_Node) then
                  declare
                     K    : constant Item_Enum := B.Kind;
                     Name : constant W_Identifier_Id :=
                       B.Main.B_Name;
                     Ty   : constant W_Type_Id := Get_Typ (Name);
                  begin

                     --  If there is no Ada_Node associated to the binder then
                     --  it must be either the unit binder or a binder for
                     --  a variable referenced for effects only.

                     pragma Assert
                       (K = Regular
                        and then (Ty in
                              M_Main.Type_Of_Heap |
                              EW_Private_Type |
                              EW_Unit_Type));
                  end;
               end if;

               Pred :=
                 +New_And_Then_Expr
                 (Domain => EW_Pred,
                  Left   => +Pred,
                  Right  => +Dyn_Prop);
            end;
         end if;
      end loop;
      return Pred;
   end Compute_Guard_Formula;

   ------------------------------------
   -- Compute_Subprogram_Parameters  --
   ------------------------------------

   function Compute_Subprogram_Parameters  (E : Entity_Id; Domain : EW_Domain)
                             return Item_Array is
      Raw_Binders : constant Item_Array := Compute_Raw_Binders (E);
   begin
      return (if Domain = EW_Prog then Raw_Binders
              else Add_Logic_Binders (E, Raw_Binders));
   end Compute_Subprogram_Parameters;

   -----------------------
   -- Add_Logic_Binders --
   -----------------------

   function Add_Logic_Binders (E           : Entity_Id;
                               Raw_Binders : Item_Array)
                                     return Item_Array is
      Num_Binders : Integer;
      Count       : Integer;

      Read_Ids    : Flow_Types.Flow_Id_Sets.Set;
      Write_Ids   : Flow_Types.Flow_Id_Sets.Set;
      Read_Names  : Name_Sets.Set;

   begin
      --  Collect global variables potentially read

      Flow_Utility.Get_Proof_Globals (Subprogram => E,
                                      Classwide  => True,
                                      Reads      => Read_Ids,
                                      Writes     => Write_Ids);
      Read_Names := Flow_Types.To_Name_Set (Read_Ids);

      --  If E has no parameters and no read effects, return a singleton of
      --  unit type.

      Num_Binders := Raw_Binders'Length + Integer (Read_Names.Length);

      declare
         Result : Item_Array (1 .. Num_Binders);

      begin
         --  First, copy all binders for parameters of E

         Result (1 .. Raw_Binders'Length) := Raw_Binders;

         --  Next, add binders for read effects of E

         Count := Raw_Binders'Length + 1;
         for R of Read_Names loop
            declare
               Entity : constant Entity_Id := Find_Entity (R);
            begin
               --  For state abstractions pretend there is no Entity

               if Present (Entity)
                 and then not (Ekind (Entity) = E_Abstract_State)
                 and then Entity_In_SPARK (Entity)
               then
                  Result (Count) :=
                    (Regular,
                     (Ada_Node => Entity,
                      B_Name   =>
                        New_Identifier
                          (Name => Full_Name (Entity),
                           Typ  => Type_Of_Node (Etype (Entity))),
                      B_Ent    => Null_Entity_Name,
                      Mutable  => False));
               else
                  Result (Count) :=
                    (Regular,
                     (Ada_Node => Empty,
                      B_Name   =>
                        New_Identifier
                          (Name => To_String (R),
                           Typ  => To_Why_Type (To_String (R))),
                      B_Ent    => R,
                      Mutable  => False));
               end if;
            end;
            Count := Count + 1;
         end loop;

         return Result;
      end;
   end Add_Logic_Binders;

   -------------------------
   -- Compute_Raw_Binders --
   -------------------------

   function Compute_Raw_Binders (E : Entity_Id) return Item_Array is
      Params        : constant List_Id :=
        (if Is_Entry (E) then Parameter_Specifications (Parent (E))
         else Parameter_Specifications (Subprogram_Specification (E)));
      Ada_Param_Len : constant Integer := Integer (List_Length (Params));
      Binder_Len    : constant Integer :=
        (if Is_Protected_Subprogram (E) then Ada_Param_Len + 1
         else Ada_Param_Len);
      Result        : Item_Array (1 .. Binder_Len);
      Param         : Node_Id;
      Count         : Integer;
   begin
      Param := First (Params);
      Count := 1;
      if Is_Protected_Subprogram (E) then
         declare
            Prot : constant Entity_Id := Containing_Protected_Type (E);
         begin
            Result (1) := (Prot_Self, Protected_Self_Binder (Prot));
            Count := 2;
         end;
      end if;
      while Present (Param) loop
         Result (Count) := Mk_Item_Of_Entity
           (E           => Defining_Identifier (Param),
            Local       => True,
            In_Fun_Decl => True);
         Next (Param);
         Count := Count + 1;
      end loop;

      return Result;
   end Compute_Raw_Binders;

   --------------------------------------
   -- Compute_Contract_Cases_Guard_Map --
   --------------------------------------

   --  Pragma/aspect Contract_Cases (Guard1 => Consequence1,
   --                                Guard2 => Consequence2,
   --                                  ...
   --                                GuardN => ConsequenceN
   --                              [,OTHERS => ConsequenceN+1]);

   --  This helper subprogram stores in Guard_Map a map from guard expressions
   --  to temporary Why names. The temporary Why name for the OTHERS case
   --  is stored in Others_Guard_Ident, and the value of this guard in
   --  Others_Guard_Expr. These results will be used to generate bindings
   --  such as:

   --    let guard1 = ... in
   --    let guard2 = ... in
   --    ...
   --    let guardN = ... in
   --    let guardOTHERS = not (guard1 or guard2 ... or guardN) in

   procedure Compute_Contract_Cases_Guard_Map
     (E                  : Entity_Id;
      Guard_Map          : out Ada_To_Why_Ident.Map;
      Others_Guard_Ident : out W_Identifier_Id;
      Others_Guard_Expr  : out W_Expr_Id)
   is
      Prag          : constant Node_Id :=
        Get_Pragma (E, Pragma_Contract_Cases);
      Aggr          : Node_Id;
      Contract_Case : Node_Id;
      Case_Guard    : Node_Id;

   begin
      --  Initial values for outputs related to the "others" guard if any

      Others_Guard_Ident := Why_Empty;
      Others_Guard_Expr := New_Literal (Domain => EW_Term, Value  => EW_False);

      --  If no Contract_Cases on this subprogram, nothing to do

      if No (Prag) then
         return;
      end if;

      --  Process individual contract cases

      Aggr := Expression (First (Pragma_Argument_Associations (Prag)));
      Contract_Case := First (Component_Associations (Aggr));
      while Present (Contract_Case) loop
         declare
            --  Temporary Why name for the current guard
            Guard_Ident : constant W_Identifier_Id :=
              New_Temp_Identifier (Typ => EW_Bool_Type);

            --  Whether the current guard is enabled
            Enabled     : constant W_Expr_Id := +Guard_Ident;

         begin
            Case_Guard := First (Choices (Contract_Case));

            --  The OTHERS choice requires special processing

            if Nkind (Case_Guard) = N_Others_Choice then
               Others_Guard_Ident := Guard_Ident;
               Others_Guard_Expr := New_Not (Domain => EW_Pred,
                                             Right  => Others_Guard_Expr);

            --  Regular contract case

            else
               Guard_Map.Include (Case_Guard, Guard_Ident);
               Others_Guard_Expr := New_Or_Expr (Left   => Others_Guard_Expr,
                                                 Right  => Enabled,
                                                 Domain => EW_Term);
            end if;

            Next (Contract_Case);
         end;
      end loop;
   end Compute_Contract_Cases_Guard_Map;

   -----------------------------------------
   -- Compute_Contract_Cases_Entry_Checks --
   -----------------------------------------

   --  Pragma/aspect Contract_Cases (Guard1 => Consequence1,
   --                                Guard2 => Consequence2,
   --                                  ...
   --                                GuardN => ConsequenceN
   --                              [,OTHERS => ConsequenceN+1]);

   --  leads to the generation of checks on subprogram entry. In a context
   --  where the precondition is known to hold, it is checked that no
   --  evaluation of a guard can lead to a run-time error, that no more than
   --  one guard evaluates to True (only if there are at least two non-OTHER
   --  guards), and that at least one guard evaluates to True (only in the case
   --  there is no OTHERS).

   --  Check that contract cases are disjoint only if there are at least two
   --  non-OTHER guards:

   --    assert ((if guard1 = True then 1 else 0) +
   --            (if guard2 = True then 1 else 0) +
   --            ...
   --            (if guardN = True then 1 else 0) <= 1)

   --  Check that contract cases are complete only if there is no OTHERS:

   --    assert ((if guard1 = True then 1 else 0) +
   --            (if guard2 = True then 1 else 0) +
   --            ...
   --            (if guardN = True then 1 else 0) >= 1)

   function Compute_Contract_Cases_Entry_Checks
     (E         : Entity_Id;
      Guard_Map : Ada_To_Why_Ident.Map) return W_Prog_Id
   is
      Prag          : constant Node_Id :=
        Get_Pragma (E, Pragma_Contract_Cases);
      Aggr          : Node_Id;
      Contract_Case : Node_Id;
      Case_Guard    : Node_Id;

      Has_Others  : Boolean := False;
      --  Set to True if there is an OTHERS guard

      Count       : W_Expr_Id := New_Integer_Constant (Value => Uint_0);
      --  Count of the guards enabled

      Result      : W_Prog_Id := New_Void;
      --  Why program for these checks

   --  Start of processing for Compute_Contract_Cases_Entry_Checks

   begin
      --  If no Contract_Cases on this subprogram, return the void program

      if No (Prag) then
         return Result;
      end if;

      --  Process individual contract cases

      Aggr := Expression (First (Pragma_Argument_Associations (Prag)));
      Contract_Case := First (Component_Associations (Aggr));
      while Present (Contract_Case) loop
         Case_Guard := First (Choices (Contract_Case));

         --  The OTHERS choice requires special processing

         if Nkind (Case_Guard) = N_Others_Choice then
            Has_Others := True;

         --  Regular contract case

         else
            declare
               Guard_Ident : constant W_Identifier_Id :=
                 Guard_Map.Element (Case_Guard);
               --  Temporary Why name for the current guard

               --  Whether the current guard is enabled
               Enabled     : constant W_Expr_Id :=
                 New_Conditional
                   (Ada_Node    => Case_Guard,
                    Domain      => EW_Term,
                    Condition   =>
                      New_Call
                        (Domain => EW_Pred,
                         Name   => Why_Eq,
                         Args   => (1 => +Guard_Ident,
                                    2 => New_Literal (Domain => EW_Term,
                                                      Value  => EW_True)),
                         Typ    => EW_Bool_Type),
                    Then_Part   => New_Integer_Constant (Value => Uint_1),
                    Else_Part   => New_Integer_Constant (Value => Uint_0));
            begin
               Count :=
                 New_Call
                   (Ada_Node => Case_Guard,
                    Domain   => EW_Term,
                    Name     => Int_Infix_Add,
                    Args     => (1 => Count, 2 => Enabled),
                    Typ      => EW_Int_Type);
            end;
         end if;

         Next (Contract_Case);
      end loop;

      --  A check that contract cases are disjoint is generated only when there
      --  are at least two guards, and none is an OTHER guard.

      if List_Length (Component_Associations (Aggr)) >= 2
        and then (if List_Length (Component_Associations (Aggr)) = 2
                  then not Has_Others)
      then
         Result := Sequence
           (Result,
            New_Assert
              (Pred     =>
                   +New_VC_Expr
                 (Prag,
                  New_Call
                    (Name => Int_Infix_Le,
                     Typ  => EW_Bool_Type,
                     Domain => EW_Pred,
                     Args =>
                       (+Count, New_Integer_Constant (Value => Uint_1))),
                  VC_Disjoint_Contract_Cases,
                  EW_Pred),
            Assert_Kind => EW_Check));
      end if;

      --  A check that contract cases are complete is generated only when there
      --  is no OTHER guard.

      if not Has_Others then
         Result := Sequence
           (Result,
            New_Assert
              (Pred       =>
                   +New_VC_Expr
                 (Prag,
                  New_Call
                    (Domain => EW_Pred,
                     Typ    => EW_Bool_Type,
                     Name   => Int_Infix_Ge,
                     Args => (+Count,
                              New_Integer_Constant (Value => Uint_1))),
                  VC_Complete_Contract_Cases,
                  EW_Pred),
               Assert_Kind => EW_Check));
      end if;

      return New_Ignore (Prog => Result);
   end Compute_Contract_Cases_Entry_Checks;

   ----------------------------------------
   -- Compute_Contract_Cases_Exit_Checks --
   ----------------------------------------

   --  Pragma/aspect Contract_Cases (Guard1 => Consequence1,
   --                                Guard2 => Consequence2,
   --                                  ...
   --                                GuardN => ConsequenceN
   --                              [,OTHERS => ConsequenceN+1]);

   --  leads to the generation of checks on subprogram exit. It is checked that
   --  the consequence for the guard that was True on entry also evaluates to
   --  True, without run-time errors.

   --    assert (if guard1 then consequence1);
   --    assert (if guard2 then consequence2);
   --    ...
   --    assert (if guardN then consequenceN);
   --    assert (if not (guard1 or guard2 ... or guardN) then consequenceN+1);

   function Compute_Contract_Cases_Exit_Checks
     (Params             : Transformation_Params;
      E                  : Entity_Id;
      Guard_Map          : Ada_To_Why_Ident.Map;
      Others_Guard_Ident : W_Identifier_Id) return W_Prog_Id
   is
      Prag          : constant Node_Id :=
        Get_Pragma (E, Pragma_Contract_Cases);
      Aggr          : Node_Id;
      Contract_Case : Node_Id;
      Case_Guard    : Node_Id;

      function Do_One_Contract_Case
        (Contract_Case : Node_Id;
         Enabled       : W_Expr_Id) return W_Prog_Id;
      --  Returns the Why program checking absence of run-time errors and
      --  function verification of the given Contract_Case. Enabled is a
      --  boolean term.

      function Do_One_Contract_Case
        (Contract_Case : Node_Id;
         Enabled       : W_Expr_Id) return W_Prog_Id
      is
         Consequence  : constant Node_Id := Expression (Contract_Case);

         --  Enabled must be converted to a predicate to be used as the
         --  condition in an if-expr inside a predicate.
         Enabled_Pred : constant W_Expr_Id :=
           New_Call
             (Domain => EW_Pred,
              Name   => Why_Eq,
              Typ    => EW_Bool_Type,
              Args   => (+Enabled,
                         New_Literal (Domain => EW_Term,
                                      Value  => EW_True)));
      begin
         return Sequence
           (New_Ignore
              (Prog =>
                 +W_Expr_Id'(New_Conditional
                   (Ada_Node    => Contract_Case,
                    Domain      => EW_Prog,
                    Condition   => Enabled,
                    Then_Part   =>
                      +Transform_Expr (Consequence, EW_Prog, Params),
                    Else_Part   =>
                      New_Literal (Domain => EW_Prog,
                                   Value  => EW_True)))),
            New_Assert
              (Pred => +New_VC_Expr
                 (Contract_Case,
                  New_Conditional
                    (Ada_Node    => Contract_Case,
                     Domain      => EW_Pred,
                     Condition   => Enabled_Pred,
                     Then_Part   =>
                       +Transform_Expr (Consequence, EW_Pred, Params)),
                    VC_Contract_Case,
                    EW_Pred),
               Assert_Kind => EW_Assert));
      end Do_One_Contract_Case;

      Result : W_Prog_Id := New_Void;

   --  Start of processing for Compute_Contract_Cases_Exit_Checks

   begin
      --  If no Contract_Cases on this subprogram, return

      if No (Prag) then
         return Result;
      end if;

      --  Process individual contract cases

      Aggr := Expression (First (Pragma_Argument_Associations (Prag)));
      Contract_Case := First (Component_Associations (Aggr));
      while Present (Contract_Case) loop
         Case_Guard := First (Choices (Contract_Case));

         declare
            --  Temporary Why name for the current guard
            Guard_Ident : constant W_Identifier_Id :=
              (if Nkind (Case_Guard) = N_Others_Choice then
                 Others_Guard_Ident
               else
                 Guard_Map.Element (Case_Guard));

            --  Whether the current guard is enabled
            Enabled     : constant W_Expr_Id := +Guard_Ident;

         begin
            Result := Sequence
              (Result, Do_One_Contract_Case (Contract_Case, Enabled));
         end;

         Next (Contract_Case);
      end loop;

      return Result;
   end Compute_Contract_Cases_Exit_Checks;

   ------------------------------------------
   -- Compute_Contract_Cases_Postcondition --
   ------------------------------------------

   --  Pragma/aspect Contract_Cases (Guard1 => Consequence1,
   --                                Guard2 => Consequence2,
   --                                  ...
   --                                GuardN => ConsequenceN
   --                              [,OTHERS => ConsequenceN+1]);

   --  leads to the generation of a postcondition for the corresponding Why
   --  program function.

   --    if guard1 then consequence1
   --    else if guard2 then consequence2
   --    ...
   --    else if guardN then consequenceN
   --    [else consequenceN+1]

   function Compute_Contract_Cases_Postcondition
     (Params : Transformation_Params;
      E      : Entity_Id) return W_Pred_Id
   is
      Prag          : constant Node_Id :=
        Get_Pragma (E, Pragma_Contract_Cases);
      Aggr          : Node_Id;
      Contract_Case : Node_Id;
      Case_Guard    : Node_Id;
      Consequence   : Node_Id;

      Result : W_Pred_Id := New_Literal (Value => EW_True);

   --  Start of processing for Compute_Contract_Cases_Postcondition

   begin
      --  If no Contract_Cases on this subprogram, return True

      if No (Prag) then
         return Result;
      end if;

      --  Process individual contract cases in reverse order, to create the
      --  proper if-elsif Why predicate.

      Aggr := Expression (First (Pragma_Argument_Associations (Prag)));
      Contract_Case := Last (Component_Associations (Aggr));
      while Present (Contract_Case) loop
         Case_Guard := First (Choices (Contract_Case));
         Consequence := Expression (Contract_Case);

         --  The "others" choice requires special processing

         if Nkind (Case_Guard) = N_Others_Choice then
            Result := +Transform_Expr (Consequence, EW_Pred, Params);

         --  Regular contract case

         else
            declare
               --  Whether the current guard is enabled in the pre-state

               Enabled : constant W_Expr_Id :=
                 Transform_Attribute_Old (Case_Guard, EW_Pred, Params);
            begin
               Result := New_Conditional
                 (Condition   => Enabled,
                  Then_Part   =>
                    +Transform_Expr (Consequence, EW_Pred, Params),
                  Else_Part   => +Result);
            end;
         end if;

         Prev (Contract_Case);
      end loop;

      return Result;
   end Compute_Contract_Cases_Postcondition;

   ------------------------------------------
   -- Generate_VCs_For_Package_Elaboration --
   ------------------------------------------

   procedure Generate_VCs_For_Package_Elaboration
     (File : in out Why_Section;
      E    : Entity_Id)
   is
      Name       : constant String  := Full_Name (E);
      Spec_N     : constant Node_Id := Package_Specification (E);
      Body_N     : constant Node_Id := Package_Body (E);
      Vis_Decls  : constant List_Id := Visible_Declarations (Spec_N);
      Priv_Decls : constant List_Id := Private_Declarations (Spec_N);
      Init_Cond  : constant Node_Id :=
        Get_Pragma (E, Pragma_Initial_Condition);
      Params     : Transformation_Params;

      Why_Body   : W_Prog_Id := New_Void;
      Post       : W_Pred_Id;

   begin
      --  We open a new theory, so that the context is fresh for that package

      Open_Theory (File,
                   New_Module
                     (Name => NID (Name & "__package_def"),
                      File => No_Name),
                   Comment =>
                     "Module for checking absence of run-time errors and "
                       & "package initial condition on package elaboration of "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);
      Current_Subp := E;

      Params := (File        => File.File,
                 Theory      => File.Cur_Theory,
                 Phase       => Generate_VCs_For_Body,
                 Gen_Marker  => False,
                 Ref_Allowed => True);

      --  Translate initial condition of E

      if Present (Init_Cond) then
         declare
            Expr : constant Node_Id :=
              Expression (First (Pragma_Argument_Associations (Init_Cond)));
         begin
            --  Generate postcondition for generated subprogram, that
            --  corresponds to the initial condition of the package.

            Params.Phase := Generate_Contract_For_Body;
            Post := +Transform_Expr (Expr, EW_Bool_Type, EW_Pred, Params);
            Post :=
              +New_VC_Expr (Init_Cond, +Post, VC_Initial_Condition, EW_Pred);

            --  Generate program to check the absence of run-time errors in the
            --  initial condition.

            Params.Phase := Generate_VCs_For_Contract;
            Why_Body :=
              +Transform_Expr (Expr, EW_Bool_Type, EW_Prog, Params);
         end;

      --  No initial condition, so no postcondition for the generated
      --  subprogram.

      else
         Post := True_Pred;
      end if;

      --  Translate declarations and statements in the package body, if there
      --  is one.

      if Present (Body_N) then
         if Present (Handled_Statement_Sequence (Body_N)) then
            Why_Body :=
              Sequence
                (Transform_Statements_And_Declarations
                   (Statements (Handled_Statement_Sequence (Body_N))),
                 Why_Body);
         end if;

         Why_Body :=
           Transform_Declarations_Block (Declarations (Body_N), Why_Body);
      end if;

      --  Translate public and private declarations of the package

      if Present (Priv_Decls) then
         Why_Body := Transform_Declarations_Block (Priv_Decls, Why_Body);
      end if;

      if Present (Vis_Decls) then
         Why_Body := Transform_Declarations_Block (Vis_Decls, Why_Body);
      end if;

      --  We assume that objects used in the program are in range, if
      --  they are of a dynamic type.

      Why_Body :=
        Sequence
          (Compute_Dynamic_Property_For_Inputs (Params => Params,
                                                E      => E),
           Why_Body);

      --  Assume values of constants

      Assume_Value_Of_Constants (Why_Body, E, Params);

      declare
         Label_Set : Name_Id_Set := Name_Id_Sets.To_Set (Cur_Subp_Sloc);
      begin
         Label_Set.Include (NID ("W:diverges:N"));
         Emit (File.Cur_Theory,
                Why.Gen.Binders.New_Function_Decl
                 (Domain  => EW_Prog,
                  Name    => Def_Name,
                  Binders => (1 => Unit_Param),
                  Labels  => Label_Set,
                  Post    => Post,
                  Def     => +Why_Body));
      end;

      Close_Theory (File,
                    Kind => VC_Generation_Theory);
   end Generate_VCs_For_Package_Elaboration;

   --------------------------
   -- Generate_VCs_For_LSP --
   --------------------------

   procedure Generate_VCs_For_LSP
     (File : in out Why_Section;
      E    : Entity_Id)
   is
      Name      : constant String := Full_Name (E);
      Params    : Transformation_Params;

      Inherited_Pre_List  : Node_Lists.List;
      Classwide_Pre_List  : Node_Lists.List;
      Pre_List            : Node_Lists.List;
      Inherited_Post_List : Node_Lists.List;
      Classwide_Post_List : Node_Lists.List;
      Post_List           : Node_Lists.List;

      Inherited_Pre_Spec   : W_Pred_Id;
      Classwide_Pre_Spec   : W_Pred_Id;
      Pre_Spec             : W_Pred_Id;
      Inherited_Post_Spec  : W_Pred_Id;
      Classwide_Post_Spec  : W_Pred_Id;
      Post_Spec            : W_Pred_Id;

      Inherited_Pre_Assume  : W_Prog_Id;
      Classwide_Pre_Check   : W_Prog_Id;
      Classwide_Pre_Assume  : W_Prog_Id;
      Pre_Check             : W_Prog_Id;
      Pre_Assume            : W_Prog_Id;
      Call_Effects          : W_Prog_Id;
      Post_Assume           : W_Prog_Id;
      Classwide_Post_Check  : W_Prog_Id;
      Classwide_Post_Assume : W_Prog_Id;
      Inherited_Post_Check  : W_Prog_Id;

      Why_Body                : W_Prog_Id := New_Void;
      Classwide_Pre_RTE       : W_Prog_Id := New_Void;
      Classwide_Weaker_Pre    : W_Prog_Id := New_Void;
      Weaker_Pre              : W_Prog_Id := New_Void;
      Stronger_Post           : W_Prog_Id := New_Void;
      Classwide_Post_RTE      : W_Prog_Id := New_Void;
      Stronger_Classwide_Post : W_Prog_Id := New_Void;

   begin
      Open_Theory (File,
                   New_Module
                     (Name => NID (Name & "__subprogram_lsp"),
                      File => No_Name),
                   Comment =>
                     "Module for checking LSP for subprogram "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Current_Subp := E;

      --  First, clear the list of translations for X'Old expressions, and
      --  create a new identifier for F'Result.

      Reset_Map_For_Old;

      if Ekind (E) = E_Function then
         Result_Name :=
           New_Identifier
             (Name => Name & "__result", Typ => Type_Of_Node (Etype (E)));
      end if;

      Params :=
        (File        => File.File,
         Theory      => File.Cur_Theory,
         Phase       => Generate_VCs_For_Contract,
         Gen_Marker  => False,
         Ref_Allowed => True);

      --  First retrieve contracts specified on the subprogram and the
      --  subprograms it overrides.

      Inherited_Pre_List := Find_Contracts
        (E, Name_Precondition, Inherited => True);
      Classwide_Pre_List := Find_Contracts
        (E, Name_Precondition, Classwide => True);
      Pre_List := Find_Contracts (E, Name_Precondition);

      Inherited_Post_List := Find_Contracts
        (E, Name_Postcondition, Inherited => True);
      Classwide_Post_List := Find_Contracts
        (E, Name_Postcondition, Classwide => True);
      Post_List := Find_Contracts (E, Name_Postcondition);

      --  Then, generate suitable predicates based on the specified contracts,
      --  with appropriate True defaults.

      Inherited_Pre_Spec :=
        +Compute_Spec (Params, Inherited_Pre_List, EW_Pred);
      Classwide_Pre_Spec :=
        +Compute_Spec (Params, Classwide_Pre_List, EW_Pred);
      Pre_Spec := +Compute_Spec (Params, Pre_List, EW_Pred);

      Inherited_Post_Spec :=
        +Compute_Spec (Params, Inherited_Post_List, EW_Pred);
      Classwide_Post_Spec :=
        +Compute_Spec (Params, Classwide_Post_List, EW_Pred);
      Post_Spec := +Compute_Spec (Params, Post_List, EW_Pred);

      --  Compute the effect of a call of the subprogram.

      Call_Effects := New_Havoc_Statement
        (Ada_Node => E,
         Effects  => +Compute_Effects (E, Global_Params => True));

      Call_Effects := Sequence
        (Call_Effects,
         New_Assume_Statement
           (Ada_Node => E,
            Pred     => Compute_Dynamic_Property_For_Effects (E, Params)));

      --  If E has a class-wide precondition, check that it cannot raise a
      --  run-time error in an empty context.

      if not Classwide_Pre_List.Is_Empty then
         Classwide_Pre_RTE :=
           +Compute_Spec (Params, Classwide_Pre_List, EW_Prog);
         Classwide_Pre_RTE :=
           New_Abstract_Expr (Expr => Classwide_Pre_RTE, Post => True_Pred);
      end if;

      --  If E is overriding another subprogram, check that its specified
      --  classwide precondition is weaker than the inherited one.

      if Is_Overriding_Subprogram (E)
        and then not Classwide_Pre_List.Is_Empty
      then
         Inherited_Pre_Assume :=
           New_Assume_Statement (Pred => Inherited_Pre_Spec);

         Classwide_Pre_Check := New_Located_Assert
           (Ada_Node => Get_Location_For_Aspect (E, Name_Precondition,
                                                 Classwide => True),
            Pred     => Classwide_Pre_Spec,
            Reason   => VC_Weaker_Classwide_Pre,
            Kind     => EW_Assert);

         Classwide_Weaker_Pre := Sequence
           ((1 => New_Comment (Comment =>
                               NID ("Checking that class-wide precondition is"
                                  & " implied by inherited precondition")),
             2 => Inherited_Pre_Assume,
             3 => Classwide_Pre_Check));

         Classwide_Weaker_Pre :=
           New_Abstract_Expr (Expr => Classwide_Weaker_Pre, Post => True_Pred);
      end if;

      --  If E has a specific precondition, check that it is weaker than the
      --  dispatching one.

      if not Pre_List.Is_Empty then
         Classwide_Pre_Assume :=
           New_Assume_Statement (Pred =>
             Get_Dispatching_Contract (Params, E, Name_Precondition));

         Pre_Check := New_Located_Assert
           (Ada_Node => Get_Location_For_Aspect (E, Name_Precondition),
            Pred     => Pre_Spec,
            Reason   => (if Classwide_Pre_List.Is_Empty and
                            Inherited_Pre_List.Is_Empty
                         then
                           VC_Trivial_Weaker_Pre
                         else
                           VC_Weaker_Pre),
            Kind     => EW_Assert);

         Weaker_Pre := Sequence
           ((1 => New_Comment (Comment =>
                               NID ("Checking that precondition is"
                                  & " implied by class-wide precondition")),
             2 => Classwide_Pre_Assume,
             3 => Pre_Check));

         Weaker_Pre :=
           New_Abstract_Expr (Expr => Weaker_Pre, Post => True_Pred);
      end if;

      --  If E has a specific postcondition, check that it is stronger than the
      --  dispatching one. To that end, perform equivalent effects of call in
      --  context of precondition for static call.
      --  Skip this check if the dispatching postcondition is the default True
      --  postcondition.

      if not Post_List.Is_Empty
        and then not (Classwide_Post_List.Is_Empty
                        and then
                      Inherited_Post_List.Is_Empty)
      then
         Pre_Assume :=
           New_Assume_Statement (Pred =>
             Get_Static_Call_Contract (Params, E, Name_Precondition));

         Post_Assume := New_Assume_Statement (Pred => Post_Spec);

         Classwide_Post_Check := New_Located_Assert
           (Ada_Node => Get_Location_For_Aspect (E, Name_Postcondition),
            Pred     =>
              Get_Dispatching_Contract (Params, E, Name_Postcondition),
            Reason   => VC_Stronger_Post,
            Kind     => EW_Assert);

         Stronger_Post := Sequence
           ((1 => New_Comment (Comment =>
                                 NID ("Simulate static call to subprogram "
                                 & """" & Get_Name_String (Chars (E)) & """")),
             2 => Pre_Assume,
             3 => Call_Effects,
             4 => New_Comment (Comment =>
                               NID ("Checking that class-wide postcondition is"
                                  & " implied by postcondition")),
             5 => Post_Assume,
             6 => Classwide_Post_Check));

         Stronger_Post :=
           New_Abstract_Expr (Expr => Stronger_Post, Post => True_Pred);
      end if;

      --  If E is overriding another subprogram, check that its specified
      --  classwide postcondition is stronger than the inherited one. Also
      --  check that the class-wide postcondition cannot raise runtime errors.
      --  To that end, perform equivalent effects of call in an empty context.
      --  Note that we should *not* assume the dispatching precondition for
      --  this check, as this would not be transitive.

      if not Classwide_Post_List.Is_Empty then
         Classwide_Post_RTE :=
           +Compute_Spec (Params, Classwide_Post_List, EW_Prog);
         Classwide_Post_RTE :=
           New_Abstract_Expr (Expr => Classwide_Post_RTE, Post => True_Pred);
         Classwide_Post_RTE := Sequence
           ((1 => Call_Effects,
             2 => Classwide_Post_RTE));

         if Is_Overriding_Subprogram (E) then
            Classwide_Post_Assume :=
              New_Assume_Statement (Pred => Classwide_Post_Spec);

            Inherited_Post_Check := New_Located_Assert
              (Ada_Node => Get_Location_For_Aspect (E, Name_Postcondition,
                                                    Classwide => True),
               Pred     => Inherited_Post_Spec,
               Reason   => VC_Stronger_Classwide_Post,
               Kind     => EW_Assert);

            Stronger_Classwide_Post := Sequence
              ((1 => New_Comment (Comment =>
                               NID ("Checking that inherited postcondition is"
                                  & " implied by class-wide postcondition")),
                2 => Call_Effects,
                3 => Classwide_Post_Assume,
                4 => Inherited_Post_Check));

            Stronger_Classwide_Post :=
              New_Abstract_Expr
                (Expr => Stronger_Classwide_Post, Post => True_Pred);
         end if;
      end if;

      Why_Body := Sequence
        ((1 => Classwide_Pre_RTE,
          2 => Classwide_Weaker_Pre,
          3 => Weaker_Pre,
          4 => Stronger_Post,
          5 => Classwide_Post_RTE,
          6 => Stronger_Classwide_Post));

      --  Assume dynamic property of inputs before the checks

      Why_Body := Sequence
        (Compute_Dynamic_Property_For_Inputs (Params => Params,
                                              E      => E),
         Why_Body);

      --  Assume values of constants

      Assume_Value_Of_Constants (Why_Body, E, Params);

      --  Declare a global variable to hold the result of a function

      if Ekind (E) = E_Function then
         Emit
           (File.Cur_Theory,
            New_Global_Ref_Declaration
              (Name     => Result_Name,
               Labels   => Get_Counterexample_Labels (E),
               Ref_Type => Type_Of_Node (Etype (E))));
      end if;

      --  add declarations for 'Old variables

      Why_Body := Bind_From_Mapping_In_Expr
        (Params                 => Params,
         Map                    => Map_For_Old,
         Expr                   => Why_Body,
         Do_Runtime_Error_Check => False,
         Bind_Value_Of_Old      => True);

      declare
         Label_Set : Name_Id_Set := Name_Id_Sets.To_Set (Cur_Subp_Sloc);
      begin
         Label_Set.Include (NID ("W:diverges:N"));
         Emit (File.Cur_Theory,
               Why.Gen.Binders.New_Function_Decl
                 (Domain  => EW_Prog,
                  Name    => Def_Name,
                  Binders => (1 => Unit_Param),
                  Labels  => Label_Set,
                  Def     => +Why_Body));
      end;

      --  We should *not* filter our own entity, it is needed for recursive
      --  calls

      Close_Theory (File,
                    Kind => VC_Generation_Theory,
                    Defined_Entity => E);
   end Generate_VCs_For_LSP;

   ---------------------------------
   -- Generate_VCs_For_Subprogram --
   ---------------------------------

   procedure Generate_VCs_For_Subprogram
     (File : in out Why_Section;
      E    : Entity_Id)
   is
      Name      : constant String := Full_Name (E);
      Params    : Transformation_Params;

      Body_N    : constant Node_Id :=
        (if Is_Entry (E) then Entry_Body (E) else Subprogram_Body (E));
      Post_N    : Node_Id;
      Assume    : W_Prog_Id;
      Init_Prog : W_Prog_Id;
      Prog      : W_Prog_Id;
      Why_Body  : W_Prog_Id;
      Post      : W_Pred_Id;

      --  Mapping from guards to temporary names, and Why program to check
      --  contract cases on exit.
      Guard_Map          : Ada_To_Why_Ident.Map;
      Others_Guard_Ident : W_Identifier_Id;
      Others_Guard_Expr  : W_Expr_Id;

      Contract_Check : W_Prog_Id;
      Post_Check     : W_Prog_Id;
      Precondition   : W_Prog_Id;
      Entry_Havoc    : W_Prog_Id;

      Result_Var : W_Prog_Id;

   begin
      Open_Theory (File,
                   New_Module
                     (Name => NID (Name & "__subprogram_def"),
                      File => No_Name),
                   Comment =>
                     "Module for checking contracts and absence of "
                       & "run-time errors in subprogram "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Current_Subp := E;

      --  There might be no specific postcondition for E. In that case, the
      --  classwide or inherited postcondition is checked if present. Locate
      --  it on E for the inherited case.

      if Has_Contracts (E, Name_Postcondition) then
         Post_N := Get_Location_For_Aspect (E, Name_Postcondition);
      elsif Has_Contracts (E, Name_Postcondition, Classwide => True) then
         Post_N :=
          Get_Location_For_Aspect (E, Name_Postcondition, Classwide => True);
      elsif Has_Contracts (E, Name_Postcondition, Inherited => True) then
         Post_N := E;
      else
         Post_N := Empty;
      end if;

      --  First, clear the list of translations for X'Old expressions, and
      --  create a new identifier for F'Result.

      Reset_Map_For_Old;
      if Ekind (E) = E_Function then
         Result_Name :=
           New_Identifier
             (Name => Name & "__result", Typ => Type_Of_Node (Etype (E)));
      end if;
      Result_Var :=
        (if Ekind (E) = E_Function then
              New_Deref
           (Ada_Node => Body_N,
            Right    => Result_Name,
            Typ      => Type_Of_Node (Etype (E)))
         else New_Void);

      if Is_Protected_Subprogram (E) then
         Self_Name :=
           New_Identifier
             (Name => "self__",
              Typ  => Type_Of_Node (Containing_Protected_Type (E)));
         Self_Is_Mutable := True;
      end if;

      Params :=
        (File        => File.File,
         Theory      => File.Cur_Theory,
         Phase       => Generate_VCs_For_Contract,
         Gen_Marker  => False,
         Ref_Allowed => True);

      --  The body of the subprogram may contain declarations that are in fact
      --  essential to prove absence of RTE in the pre, e.g. compiler-generated
      --  subtype declarations. We need to take those into account.

      if Present (Body_N) and then Entity_Body_In_SPARK (E) then
         Assume := Transform_Declarations_For_Params (Declarations (Body_N));
      else
         Assume := New_Void;
      end if;

      --  In the following declare block, we define the variable "Precondition"
      --  to contain the precondition assumption for this subprogram. In fact,
      --  if the subprogram is a main, the precondition needs to be *proved*,
      --  and in this case the assumption is realized using an assertion
      --  expression.

      for Expr of Get_Precondition_Expressions (E) loop
         if Nkind (Expr) = N_Identifier
           and then Entity (Expr) = Standard_False
         then
            Error_Msg_N (Msg  => "?precondition is statically false",
                         N    => Expr);
         end if;
      end loop;

      declare
         Pre : constant W_Pred_Id :=
           Get_Static_Call_Contract (Params, E, Name_Precondition);
      begin
         if not Is_Entry (E) and then Might_Be_Main (E) then
            Precondition :=
              New_Located_Assert
                (Ada_Node => Get_Location_For_Aspect (E, Name_Precondition),
                 Pred     => Pre,
                 Reason   => VC_Precondition_Main,
                 Kind     => EW_Assert);
         else
            Precondition := New_Assume_Statement (Pred => Pre);
         end if;
      end;

      --  If contract cases are present, generate checks for absence of
      --  run-time errors in guards, and check that contract cases are disjoint
      --  and complete. The completeness is checked in a context where the
      --  precondition is assumed. Init_Prog is set to the program up to the
      --  precondition assumption, and Prog is set to the program starting
      --  with the contract case entry checks.

      Compute_Contract_Cases_Guard_Map
        (E                  => E,
         Guard_Map          => Guard_Map,
         Others_Guard_Ident => Others_Guard_Ident,
         Others_Guard_Expr  => Others_Guard_Expr);

      if Is_Entry (E) then
         Entry_Havoc :=
           New_Havoc_Call (Self_Name);
      else
         Entry_Havoc := New_Void;
      end if;

      Init_Prog := Sequence
        ((1 => New_Comment
          (Comment => NID ("Declarations introduced by the compiler at the"
           & " beginning of the subprogram"
           & (if Sloc (E) > 0 then " " & Build_Location_String (Sloc (E))
             else ""))),
          2 => Assume,
          3 => New_Comment
          (Comment => NID ("Check for RTE in the Pre of the subprogram"
           & (if Sloc (E) > 0 then " " & Build_Location_String (Sloc (E))
             else ""))),
          4 => New_Ignore
            (Prog => +Compute_Spec (Params, E, Name_Precondition, EW_Prog)),
          5 => New_Comment
          (Comment => NID ("Assume Pre of the subprogram"
           & (if Sloc (E) > 0 then " " & Build_Location_String (Sloc (E))
             else ""))),
          6 => Precondition,
          7 => Entry_Havoc));

      Prog := Compute_Contract_Cases_Entry_Checks (E, Guard_Map);

      if Present (Body_N) and then Entity_Body_In_SPARK (E) then
         Contract_Check := Compute_Contract_Cases_Exit_Checks
           (Params             => Params,
            E                  => E,
            Guard_Map          => Guard_Map,
            Others_Guard_Ident => Others_Guard_Ident);

         Post_Check :=
           Sequence
             (New_Ignore
                (Prog =>
                       +Compute_Spec (Params, E, Name_Postcondition, EW_Prog)),
              Contract_Check);

         --  Set the phase to Generate_Contract_For_Body from now on, so that
         --  occurrences of F'Result are properly translated as Result_Name.

         Params.Phase := Generate_Contract_For_Body;

         --  Translate contract of E. A No_Return subprogram, from the inside,
         --  has postcondition true as non termination verification is done by
         --  the frontend, but the precondition is unchanged

         if No_Return (E) then
            Post := True_Pred;
         else
            Params.Gen_Marker := True;
            Post := Get_Static_Call_Contract (Params, E, Name_Postcondition);
            Params.Gen_Marker := False;

            Post := +New_VC_Expr (Post_N, +Post, VC_Postcondition, EW_Pred);
         end if;

         --  Set the phase to Generate_VCs_For_Body from now on, so that
         --  occurrences of X'Old are properly translated as reference to
         --  the corresponding binder.

         Params.Phase := Generate_VCs_For_Body;

         --  Declare a global variable to hold the result of a function

         if Ekind (E) = E_Function then
            Emit
              (File.Cur_Theory,
               New_Global_Ref_Declaration
                 (Name     => Result_Name,
                  Labels   => Get_Counterexample_Labels (E),
                  Ref_Type => Type_Of_Node (Etype (E))));
         end if;

         --  Declare global variable to hold the state of a protected object

         if Is_Protected_Subprogram (E) then
            Emit
              (File.Cur_Theory,
               New_Global_Ref_Declaration
                 (Ada_Node    => Containing_Protected_Type (E),
                  Name        => Self_Name,
                  Labels      => Name_Id_Sets.Empty_Set,
                  Ref_Type =>
                    Type_Of_Node (Containing_Protected_Type (E))));
         end if;

         --  Translate statements in the body of the subp

         Why_Body :=
           Transform_Statements_And_Declarations
             (Statements
                (Handled_Statement_Sequence (Body_N)));

         --  Translate statements in declaration block

         Why_Body :=
           Sequence
             (Transform_Declarations_For_Body (Declarations (Body_N)),
              Why_Body);

         --  Enclose the subprogram body in a try-block, so that return
         --  statements can be translated as raising exceptions.

         declare
            Raise_Stmt : constant W_Prog_Id :=
              New_Raise
                (Ada_Node => Body_N,
                 Name     => M_Main.Return_Exc);
         begin
            Why_Body :=
              New_Try_Block
                (Prog    => Sequence (Why_Body, Raise_Stmt),
                 Handler =>
                   (1 =>
                          New_Handler
                      (Name => M_Main.Return_Exc,
                       Def  => New_Void)));
         end;

         --  Check pragmas Precondition and Postcondition in the body of the
         --  subprogram as plain assertions.

         declare
            Pre_Prags  : Node_Lists.List;
            Post_Prags : Node_Lists.List;

            procedure Get_Pre_Post_Pragmas (Decls : Node_Lists.List);
            --  Retrieve pragmas Precondition and Postcondition from the list
            --  of body declarations, and add them to Pre_Prags and Post_Prags
            --  when they do not come from aspects.

            function Transform_All_Pragmas
              (Prags : Node_Lists.List) return W_Prog_Id;
            --  Force the translation of all pragmas in Prags into Why3.

            procedure Get_Pre_Post_Pragmas (Decls : Node_Lists.List) is
            begin
               for Decl of Decls loop
                  if Is_Pragma (Decl, Pragma_Precondition) and then
                    not From_Aspect_Specification (Decl)
                  then
                     Pre_Prags.Append (Decl);

                  elsif Is_Pragma (Decl, Pragma_Postcondition) and then
                    not From_Aspect_Specification (Decl)
                  then
                     Post_Prags.Append (Decl);
                  end if;
               end loop;
            end Get_Pre_Post_Pragmas;

            function Transform_All_Pragmas
              (Prags : Node_Lists.List) return W_Prog_Id
            is
               Result : W_Prog_Id := New_Void;
            begin
               for Prag of Prags loop
                  Result :=
                    Sequence (Result, Transform_Pragma (Prag, Force => True));
               end loop;
               return Result;
            end Transform_All_Pragmas;

         begin
            Get_Pre_Post_Pragmas
              (Get_Flat_Statement_And_Declaration_List
                 (Declarations (Body_N)));
            Why_Body := Sequence
              ((1 => Transform_All_Pragmas (Pre_Prags),
                2 => New_Comment
                  (Comment => NID ("Body of the subprogram"
                   & (if Sloc (E) > 0 then
                        " " & Build_Location_String (Sloc (E))
                     else ""))),
                3 => Why_Body,
                4 => New_Comment
                  (Comment => NID ("Check additional Posts and RTE in Post of"
                   & " the subprogram"
                   & (if Sloc (E) > 0 then
                        " " & Build_Location_String (Sloc (E))
                     else ""))),
                5 => Transform_All_Pragmas (Post_Prags)));
         end;

         --  Refined_Post
         --  Encapsulate the translated body inside an abstract program with
         --  the Refined_Post as a postcondition.
         --  Assume the dynamic property of modified variables after the call.

         if Has_Contracts (E, Name_Refined_Post) then
            Why_Body :=
              Sequence
                (Why_Body,
                 New_Ignore
                   (Prog => +Compute_Spec
                      (Params, E, Name_Refined_Post, EW_Prog)));
            Why_Body :=
              New_Located_Abstract
                (Ada_Node => Get_Location_For_Aspect (E, Name_Refined_Post),
                 Expr => Why_Body,
                 Reason => VC_Refined_Post,
                 Post => +Compute_Spec
                   (Params, E, Name_Refined_Post, EW_Pred));
            Why_Body := Sequence
              (Why_Body,
               New_Assume_Statement
                 (Pred => Compute_Dynamic_Property_For_Effects (E, Params)));
         end if;

         --  check absence of runtime errors in Post and RTE + validity of
         --  contract cases

         Why_Body := Sequence
           ((1 => New_Comment
                (Comment => NID ("Check additional Pres of the subprogram"
                 & (if Sloc (E) > 0 then " " & Build_Location_String (Sloc (E))
                   else ""))),
             2 => Why_Body,
             3 => Post_Check));

         --  return the result variable, so that result = result_var in the
         --  postcondition

         Why_Body := Sequence (Why_Body, Result_Var);

         --  add declarations for 'Old variables

         Why_Body := Bind_From_Mapping_In_Expr
           (Params                 => Params,
            Map                    => Map_For_Old,
            Expr                   => Why_Body,
            Guard_Map              => Guard_Map,
            Others_Guard_Ident     => Others_Guard_Ident,
            Do_Runtime_Error_Check => True,
            Bind_Value_Of_Old      => True);

         Prog := Sequence (Prog, Why_Body);
      else
         Post := True_Pred;
      end if;

      --  Bind value of guard expressions, checking for run-time errors

      Params.Phase := Generate_VCs_For_Contract;

      if Present (Others_Guard_Ident) then
         Prog := +New_Typed_Binding (Name    => Others_Guard_Ident,
                                     Domain  => EW_Prog,
                                     Def     => Others_Guard_Expr,
                                     Context => +Prog);
      end if;

      Prog := Bind_From_Mapping_In_Expr
        (Params                 => Params,
         Map                    => Guard_Map,
         Expr                   => Prog,
         Do_Runtime_Error_Check => True);

      --  Now that identifiers for guard expressions are bound, in the correct
      --  context assuming precondition, glue together the initial part of the
      --  program and the rest of it.

      Prog := Sequence (Init_Prog, Prog);

      --  Generate assumptions for dynamic types used in the program. An
      --  exception is made for predicate functions generated by the frontend,
      --  for which we should not assume that the predicate holds for checking
      --  the absence of RTE in the predicate itself.

      declare
         Pred_Fun_Param : constant Entity_Id :=
           (if Ekind (E) in E_Function | E_Procedure
              and then Is_Predicate_Function (E)
            then
              Defining_Entity (First (Parameter_Specifications
                (Subprogram_Specification (E))))
            else
              Empty);
         Assume_For_Input : constant W_Prog_Id :=
           Compute_Dynamic_Property_For_Inputs
             (Params         => Params,
              E              => E,
              Pred_Fun_Param => Pred_Fun_Param);
      begin
         Prog := Sequence
           ((1 => New_Comment
             (Comment => NID ("Assume dynamic invariants of inputs of the"
              & " subprogram "
              & (if Sloc (E) > 0 then " " & Build_Location_String (Sloc (E))
                else ""))),
             2 => Assume_For_Input,
             3 => Prog));
      end;

      --  Assume values of constants

      Assume_Value_Of_Constants (Prog, E, Params);

      --  We always need to add the int theory as
      --  Compute_Contract_Cases_Entry_Checks may make use of the
      --  infix operators.

      Add_With_Clause (File.Cur_Theory, Int_Module, EW_Import, EW_Theory);

      declare
         Label_Set : Name_Id_Set := Name_Id_Sets.To_Set (Cur_Subp_Sloc);
      begin
         Label_Set.Include (NID ("W:diverges:N"));
         Emit (File.Cur_Theory,
               Why.Gen.Binders.New_Function_Decl
                 (Domain  => EW_Prog,
                  Name    => Def_Name,
                  Binders => (1 => Unit_Param),
                  Labels  => Label_Set,
                  Post    => Post,
                  Def     => +Prog));
      end;

      --  cleanup

      Self_Name := Why_Empty;
      Self_Is_Mutable := False;

      --  We should *not* filter our own entity, it is needed for recursive
      --  calls

      Close_Theory (File,
                    Kind => VC_Generation_Theory,
                    Defined_Entity => E);
   end Generate_VCs_For_Subprogram;

   ---------------------------
   -- Generate_VCs_For_Task --
   ---------------------------

   procedure Generate_VCs_For_Task
     (File : in out Why_Section;
      E    : Entity_Id)
   is
      Name       : constant String  := Full_Name (E);
      Body_N     : constant Node_Id := Task_Body (E);
      Params     : Transformation_Params;

      Why_Body   : W_Prog_Id := New_Void;
      Post       : W_Pred_Id;
   begin
      --  We open a new theory, so that the context is fresh for this task

      Open_Theory (File,
                   New_Module
                     (Name => NID (Name & "__task_body"),
                      File => No_Name),
                   Comment =>
                     "Module for checking absence of run-time errors and "
                       & "non-termination of task body of the task "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);
      Current_Subp := E;

      Params := (File        => File.File,
                 Theory      => File.Cur_Theory,
                 Phase       => Generate_VCs_For_Body,
                 Gen_Marker  => False,
                 Ref_Allowed => True);

      Post :=
              +New_VC_Expr (Ada_Node   => E,
                      Expr       => +False_Pred,
                      Reason     => VC_Task_Termination,
                      Domain     => EW_Pred);

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);

      --  Translate declarations and statements in the task body, if there
      --  is one.

      if Present (Body_N) then
         if Present (Handled_Statement_Sequence (Body_N)) then
            Why_Body :=
              Sequence
                (Transform_Statements_And_Declarations
                   (Statements (Handled_Statement_Sequence (Body_N))),
                 Why_Body);
         end if;

         Why_Body :=
           Transform_Declarations_Block (Declarations (Body_N), Why_Body);
      end if;

      --  We check that the call graph starting from this task respects the
      --  ceiling priority protocol.

      Why_Body :=
        Sequence
          (Check_Ceiling_Protocol (Params, E),
           Why_Body);

      --  We assume that objects used in the program are in range, if
      --  they are of a dynamic type

      Why_Body :=
        Sequence
          (Compute_Dynamic_Property_For_Inputs (Params => Params,
                                                E      => E),
           Why_Body);

      --  Assume values of constants

      Assume_Value_Of_Constants (Why_Body, E, Params);

      declare
         Label_Set : Name_Id_Set := Name_Id_Sets.To_Set (Cur_Subp_Sloc);
      begin
         Label_Set.Include (NID ("W:diverges:N"));
         Emit (File.Cur_Theory,
                Why.Gen.Binders.New_Function_Decl
                 (Domain  => EW_Prog,
                  Name    => Def_Name,
                  Binders => (1 => Unit_Param),
                  Labels  => Label_Set,
                  Post    => Post,
                  Def     => +Why_Body));
      end;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
      Close_Theory (File,
                    Kind => VC_Generation_Theory);

   end Generate_VCs_For_Task;

   -----------------------------
   -- Get_Location_For_Aspect --
   -----------------------------

   function Get_Location_For_Aspect
     (E         : Entity_Id;
      Kind      : Name_Id;
      Classwide : Boolean := False) return Node_Id is
   begin

      --  In the case of a No_Return Subprogram, there is no real location for
      --  the postcondition; simply return the subprogram entity node.

      if Kind = Name_Postcondition
        and then No_Return (E)
      then
         return E;
      end if;

      --  Pre- and postconditions are stored in reverse order in
      --  Pre_Post_Conditions, hence retrieve the last assertion in this
      --  list to get the first one in source code.

      declare
         L : constant Node_Lists.List :=
           Find_Contracts (E, Kind, Classwide => Classwide);
      begin
         if L.Is_Empty then
            return Empty;
         else
            return L.Last_Element;
         end if;
      end;
   end Get_Location_For_Aspect;

   -----------------------------
   -- Generate_Axiom_For_Post --
   -----------------------------

   procedure Generate_Axiom_For_Post
     (File : Why_Section;
      E    : Entity_Id)
   is
      Logic_Func_Binders : constant Item_Array := Compute_Binders (E, EW_Term);
      Params             : Transformation_Params;
      Pre                : W_Pred_Id;
      Post               : W_Pred_Id;
      Dispatch_Pre       : W_Pred_Id;
      Dispatch_Post      : W_Pred_Id;
      Refined_Post       : W_Pred_Id;
      Why_Type           : W_Type_Id := Why_Empty;
   begin

      if Ekind (E) in E_Procedure | Entry_Kind
        or else No_Return (E)
        or else not Is_Non_Recursive_Subprogram (E)
      then
         return;
      end if;

      Why_Type := Type_Of_Node (Etype (E));

      --  If the function has a postcondition, is not mutually recursive
      --  and is not annotated with No_Return, then generate an axiom:
      --  axiom def_axiom:
      --     forall args [f (args)]. pre (args) ->
      --           let result = f (args) in post (args)

      Params :=
        (File        => File.File,
         Theory      => File.Cur_Theory,
         Phase       => Generate_Logic,
         Gen_Marker  => False,
         Ref_Allowed => False);

      --  We fill the map of parameters, so that in the pre and post, we use
      --  local names of the parameters, instead of the global names.

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);

      for Binder of Logic_Func_Binders loop
         declare
            A : constant Node_Id :=
              (case Binder.Kind is
                  when Regular | Prot_Self => Binder.Main.Ada_Node,
                  when others  => raise Program_Error);
            --  in parameters should not be split
         begin
            pragma Assert (Present (A) or else Binder.Kind = Regular);

            if Present (A) then
               Ada_Ent_To_Why.Insert (Symbol_Table,
                                      Unique_Entity (A),
                                      Binder);
            elsif Binder.Main.B_Ent /= Null_Entity_Name then

               --  If there is no Ada_Node, this is a binder generated
               --  from an effect; we add the parameter in the name
               --  map using its unique name.

               Ada_Ent_To_Why.Insert
                 (Symbol_Table,
                  Binder.Main.B_Ent,
                  Binder);
            end if;
         end;
      end loop;

      Pre := +Compute_Spec (Params, E, Name_Precondition, EW_Pred);
      Post :=
        +New_And_Expr
        (Left   =>
           +Compute_Spec (Params, E, Name_Postcondition, EW_Pred),
         Right  => +Compute_Contract_Cases_Postcondition (Params, E),
         Domain => EW_Pred);

      if Is_Dispatching_Operation (E) then
         Dispatch_Pre :=
           Get_Dispatching_Contract (Params, E, Name_Precondition);
         Dispatch_Post :=
           Get_Dispatching_Contract (Params, E, Name_Postcondition);
      end if;

      if Has_Contracts (E, Name_Refined_Post) then
         Refined_Post := +Compute_Spec (Params, E, Name_Refined_Post, EW_Pred);
      end if;

      declare
         Logic_Why_Binders : constant Binder_Array :=
           To_Binder_Array (Logic_Func_Binders);
         Logic_Id        : constant W_Identifier_Id :=
           To_Why_Id (E, Domain => EW_Term, Local => False);
         Dispatch_Logic_Id   : constant W_Identifier_Id :=
           To_Why_Id
             (E, Domain => EW_Term, Local => False, Selector => Dispatch);
         Refine_Logic_Id     : constant W_Identifier_Id :=
           To_Why_Id
             (E, Domain => EW_Term, Local => False, Selector => Refine);
         Guard   : constant W_Pred_Id :=
           Compute_Guard_Formula (Logic_Func_Binders);
         --  Dynamic property of the result.
         Dynamic_Prop_Result : constant W_Pred_Id :=
           Compute_Dynamic_Invariant (Expr     => +New_Result_Ident (Why_Type),
                                      Ty       => Etype (E),
                                      Only_Var => False_Term);

         procedure Emit_Post_Axiom
           (Suffix : String;
            Id     : W_Identifier_Id;
            Pre, Post : W_Pred_Id);
         --  emit the post_axiom with the given axiom_suffix, id, pre and post

         ---------------------
         -- Emit_Post_Axiom --
         ---------------------

         procedure Emit_Post_Axiom
           (Suffix : String;
            Id     : W_Identifier_Id;
            Pre, Post : W_Pred_Id) is
            Complete_Post : constant W_Pred_Id :=
              +New_And_Expr
              (Left   => +Post,
               Right  => +Dynamic_Prop_Result,
               Domain => EW_Pred);
         begin
            if not Is_True_Boolean (+Complete_Post) then
               Emit
                 (File.Cur_Theory,
                  New_Guarded_Axiom
                    (Ada_Node => Empty,
                     Name     => NID (Short_Name (E) & "__" & Suffix),
                     Binders  => Logic_Why_Binders,
                     Triggers =>
                       New_Triggers
                         (Triggers =>
                              (1 => New_Trigger
                                 (Terms =>
                                    (1 => New_Call
                                         (Domain  => EW_Term,
                                          Name    => Id,
                                          Binders => Logic_Why_Binders))))),
                     Pre      =>
                       +New_And_Expr (Left   => +Guard,
                                      Right  => +Pre,
                                      Domain => EW_Pred),
                     Def      =>
                       +New_Typed_Binding
                       (Ada_Node => Empty,
                        Domain   => EW_Pred,
                        Name     => +New_Result_Ident (Why_Type),
                        Def      => New_Call
                          (Domain  => EW_Term,
                           Name    => Id,
                           Binders => Logic_Why_Binders),
                        Context  => +Complete_Post)));
            end if;
         end Emit_Post_Axiom;

      --  Start of processing for Generate_Axiom_For_Post

      begin
         --  ??? clean up this code duplication for dispatch and refine

         Emit_Post_Axiom (Post_Axiom, Logic_Id, Pre, Post);

         if Is_Dispatching_Operation (E) then
            Emit_Post_Axiom (Post_Dispatch_Axiom,
                             Dispatch_Logic_Id,
                             Dispatch_Pre,
                             Dispatch_Post);
         end if;

         if Has_Contracts (E, Name_Refined_Post) then
            Emit_Post_Axiom (Post_Refine_Axiom,
                             Refine_Logic_Id,
                             Pre,
                             Refined_Post);
         end if;
      end;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
   end Generate_Axiom_For_Post;

   ------------------------------------
   -- Generate_Subprogram_Completion --
   ------------------------------------

   procedure Generate_Subprogram_Completion
     (File : in out Why_Section;
      E    : Entity_Id) is
   begin
      Open_Theory (File, E_Axiom_Module (E),
                   Comment =>
                     "Module for declaring a program function (and possibly "
                       & "an axiom) for "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                   & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Add_Dependencies_For_Effects (File.Cur_Theory, E);

      --  Store an appropriate value for the result identifier in Result_Name.

      if Ekind (E) = E_Function then
         Result_Name := New_Result_Ident (Type_Of_Node (Etype (E)));
      end if;

      Generate_Subprogram_Program_Fun (File, E);

      Generate_Axiom_For_Post (File, E);

      Close_Theory (File,
                    Kind => Axiom_Theory,
                    Defined_Entity => E);
   end Generate_Subprogram_Completion;

   --------------------------------------
   -- Generate_Subprogram_Program_Fun --
   --------------------------------------

   procedure Generate_Subprogram_Program_Fun
     (File : Why_Section;
      E    : Entity_Id)
   is
      Logic_Func_Binders : constant Item_Array := Compute_Binders (E, EW_Term);
      Func_Binders       : constant Item_Array := Compute_Binders (E, EW_Prog);
      Func_Why_Binders   : constant Binder_Array :=
        To_Binder_Array (Func_Binders);
      Params             : Transformation_Params;
      Effects            : W_Effects_Id;
      Pre                : W_Pred_Id;
      Post               : W_Pred_Id;
      Dispatch_Pre       : W_Pred_Id;
      Dispatch_Post      : W_Pred_Id;
      Refined_Post       : W_Pred_Id;
      Prog_Id            : constant W_Identifier_Id :=
        To_Why_Id (E, Domain => EW_Prog, Local => True);
      Why_Type           : W_Type_Id := Why_Empty;

   begin
      Params :=
        (File        => File.File,
         Theory      => File.Cur_Theory,
         Phase       => Generate_Logic,
         Gen_Marker  => False,
         Ref_Allowed => True);

      --  We fill the map of parameters, so that in the pre and post, we use
      --  local names of the parameters, instead of the global names

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);

      for Binder of Func_Binders loop
         declare
            A : constant Node_Id := Get_Ada_Node_From_Item (Binder);
         begin

            --  If the Ada_Node is empty, it's not an interesting binder
            --  (e.g. void_param)

            if Present (A) and then not Is_Type (E) then
               Ada_Ent_To_Why.Insert (Symbol_Table, A, Binder);
            end if;
         end;
      end loop;

      Effects := Compute_Effects (E);

      Pre := Get_Static_Call_Contract (Params, E, Name_Precondition);

      if Is_Dispatching_Operation (E) then
         Dispatch_Pre :=
           Get_Dispatching_Contract (Params, E, Name_Precondition);
      end if;

      --  For a subprogram marked with No_Return, the postcondition at call
      --  site should be "False", so that it is known in the caller that the
      --  call does not return.

      if No_Return (E) then
         Post := False_Pred;

         if Is_Dispatching_Operation (E) then
            Dispatch_Post := False_Pred;
         end if;

         if Has_Contracts (E, Name_Refined_Post) then
            Refined_Post := False_Pred;
         end if;

      --  In other cases, the postcondition is extracted from the subprogram
      --  contract.

      else
         Post :=
           +New_And_Expr
           (Left   =>
              +Get_Static_Call_Contract (Params, E, Name_Postcondition),
            Right  => +Compute_Contract_Cases_Postcondition (Params, E),
            Domain => EW_Pred);

         if Is_Dispatching_Operation (E) then
            Dispatch_Post :=
              Get_Dispatching_Contract (Params, E, Name_Postcondition);
         end if;

         if Has_Contracts (E, Name_Refined_Post) then
            Refined_Post :=
              Get_Static_Call_Contract (Params, E, Name_Refined_Post);
         end if;
      end if;

      if Ekind (E) = E_Function then

         Why_Type := Type_Of_Node (Etype (E));

         declare
            Logic_Why_Binders   : constant Binder_Array :=
              To_Binder_Array (Logic_Func_Binders);
            Logic_Func_Args     : constant W_Expr_Array :=
              Compute_Args (E, Logic_Why_Binders);
            Logic_Id            : constant W_Identifier_Id :=
              To_Why_Id (E, Domain => EW_Term, Local => False);
            Dispatch_Logic_Id   : constant W_Identifier_Id :=
              To_Why_Id
                (E, Domain => EW_Term, Local => False, Selector => Dispatch);
            Refine_Logic_Id     : constant W_Identifier_Id :=
              To_Why_Id
                (E, Domain => EW_Term, Local => False, Selector => Refine);
            Dynamic_Prop_Result : constant W_Pred_Id :=
              +Compute_Dynamic_Invariant
                 (Expr     => +New_Result_Ident (Why_Type),
                  Ty       => Etype (E),
                  Only_Var => False_Term);
            Expr_Fun_N          : constant Node_Id :=
              Get_Expression_Function (E);

            Volatile_State  : constant W_Identifier_Id :=
              New_Identifier
                (Domain => EW_Term,
                 Name   => "volatile__effect");

            function Create_Function_Decl
              (Logic_Id : W_Identifier_Id;
               Prog_Id  : W_Identifier_Id;
               Pre      : W_Pred_Id;
               Post     : W_Pred_Id) return W_Declaration_Id;
            --  create the function declaration with the given Logic_Id,
            --  Prog_Id, Pre and Post.

            --------------------------
            -- Create_Function_Decl --
            --------------------------

            function Create_Function_Decl
              (Logic_Id : W_Identifier_Id;
               Prog_Id  : W_Identifier_Id;
               Pre      : W_Pred_Id;
               Post     : W_Pred_Id) return W_Declaration_Id
            is
               --  Each function has in its postcondition that its result is
               --  equal to the application of the corresponding logic function
               --  to the same arguments.

               Param_Post : W_Pred_Id :=
                 +New_And_Expr
                 (Left   => +Dynamic_Prop_Result,
                  Right  => +Post,
                  Domain => EW_Pred);

               Effects : constant W_Effects_Id := New_Effects;
            begin

               --  A volatile function has an effect, and should not have the
               --  special postcondition which says it's result is equal to the
               --  logic function

               --  for a volatile function, we need to generate a dummy effect

               if Is_Volatile_Function (E) then
                  Effects_Append_To_Writes (Effects, Volatile_State);
               else
                  Param_Post :=
                    +New_And_Expr
                    (Domain => EW_Pred,
                     Left   =>
                       New_Call
                         (Name   => Why_Eq,
                          Domain => EW_Pred,
                          Typ    => EW_Bool_Type,
                          Args   => (+New_Result_Ident (Why_Type),
                                     New_Call
                                       (Domain => EW_Term,
                                        Name   => Logic_Id,
                                        Args   => Logic_Func_Args))),
                     Right  => +Param_Post);
               end if;
               return New_Function_Decl
                 (Domain      => EW_Prog,
                  Name        => Prog_Id,
                  Binders     => Func_Why_Binders,
                  Return_Type => Type_Of_Node (Etype (E)),
                  Labels      => Name_Id_Sets.Empty_Set,
                  Effects     => Effects,
                  Pre         => Pre,
                  Post        => Param_Post);
            end Create_Function_Decl;

         begin
            --  If E is an expression function, add its body to its
            --  postcodition.

            if Present (Expr_Fun_N)
              and then Entity_Body_In_SPARK (E)
              and then not No_Return (E)
            then
               declare
                  Use_Base  : constant Boolean :=
                    not Is_Standard_Boolean_Type (Etype (E))
                    and then Has_Scalar_Type (Etype (E))
                    and then Use_Base_Type_For_Type (Etype (E));
                  Eq_Ty     : constant W_Type_Id :=
                    (if Use_Base then Base_Why_Type (Etype (E))
                     else Why_Type);
                  Domain    : constant EW_Domain :=
                    (if Is_Standard_Boolean_Type (Etype (E)) then EW_Pred
                     else EW_Term);
                  Expr_Body : constant W_Expr_Id :=
                    Transform_Expr (Expression (Expr_Fun_N),
                                    Expected_Type => Eq_Ty,
                                    Domain        => Domain,
                                    Params        => Params);
                  Res_Expr  : constant W_Expr_Id :=
                    Insert_Simple_Conversion
                      (Domain         => EW_Term,
                       Expr           => +New_Result_Ident (Why_Type),
                       To             => Eq_Ty,
                       Force_No_Slide => True);
                  Eq_Expr   : constant W_Pred_Id :=
                    (if Is_Standard_Boolean_Type (Etype (E))
                     then New_Equal_Bool (+Res_Expr, +Expr_Body)
                     else New_Call (Name => Why_Eq,
                                    Args => (Res_Expr, Expr_Body),
                                    Typ  => EW_Bool_Type));
               begin
                  if Has_Contracts (E, Name_Refined_Post) then
                     Refined_Post :=
                       +New_And_Expr (+Eq_Expr, +Refined_Post, EW_Pred);
                  else
                     Post := +New_And_Expr (+Eq_Expr, +Post, EW_Pred);
                  end if;
               end;
            end if;

            if Is_Volatile_Function (E) then
               Emit
                 (File.Cur_Theory,
                  New_Global_Ref_Declaration
                    (Ada_Node => E,
                     Labels   => Name_Id_Sets.Empty_Set,
                     Name     => Volatile_State,
                     Ref_Type => EW_Private_Type));
            end if;

            Emit
              (File.Cur_Theory,
               Create_Function_Decl (Logic_Id => Logic_Id,
                                     Prog_Id  => Prog_Id,
                                     Pre      => Pre,
                                     Post     => Post));

            if Is_Dispatching_Operation (E) then
               Emit
                 (File.Cur_Theory,
                  New_Namespace_Declaration
                    (Name    => NID (To_String (WNE_Dispatch_Module)),
                     Declarations =>
                       (1 => Create_Function_Decl
                            (Logic_Id => Dispatch_Logic_Id,
                             Prog_Id  => Prog_Id,
                             Pre      => Dispatch_Pre,
                             Post     => Dispatch_Post))));
            end if;

            if Has_Contracts (E, Name_Refined_Post) then
               Emit
                 (File.Cur_Theory,
                  New_Namespace_Declaration
                    (Name    => NID (To_String (WNE_Refine_Module)),
                     Declarations =>
                       (1 => Create_Function_Decl
                            (Logic_Id => Refine_Logic_Id,
                             Prog_Id  => Prog_Id,
                             Pre      => Pre,
                             Post     => Refined_Post))));
            end if;
         end;

      --  Ekind (E) in E_Procedure | E_Entry

      else
         declare
            Dynamic_Prop_Effects : constant W_Pred_Id :=
              Compute_Dynamic_Property_For_Effects (E, Params);

         begin
            Emit
              (File.Cur_Theory,
               New_Function_Decl
                 (Domain      => EW_Prog,
                  Name        => Prog_Id,
                  Binders     => Func_Why_Binders,
                  Labels      => Name_Id_Sets.Empty_Set,
                  Return_Type => EW_Unit_Type,
                  Effects     => Effects,
                  Pre         => Pre,
                  Post        => +New_And_Expr
                    (Left   => +Post,
                     Right  => +Dynamic_Prop_Effects,
                     Domain => EW_Pred)));

            if Is_Dispatching_Operation (E) then
               Emit
                 (File.Cur_Theory,
                  New_Namespace_Declaration
                    (Name    => NID (To_String (WNE_Dispatch_Module)),
                     Declarations =>
                       (1 => New_Function_Decl
                            (Domain      => EW_Prog,
                             Name        => Prog_Id,
                             Binders     => Func_Why_Binders,
                             Labels      => Name_Id_Sets.Empty_Set,
                             Return_Type => EW_Unit_Type,
                             Effects     => Effects,
                             Pre         => Dispatch_Pre,
                             Post        => +New_And_Expr
                               (Left   => +Dispatch_Post,
                                Right  => +Dynamic_Prop_Effects,
                                Domain => EW_Pred)))));
            end if;

            --  For error-signaling procedures, define a variant of the
            --  program function with a precondition of False inside the
            --  namespace No_Return. This variant is used when calling the
            --  error-signaling procedure outside another error-signaling
            --  procedure. This ensures that a check is issued for each
            --  such call, to detect when they are reachable.

            if Is_Error_Signaling_Procedure (E) then
               Emit
                 (File.Cur_Theory,
                  New_Namespace_Declaration
                    (Name    => NID (To_String (WNE_No_Return_Module)),
                     Declarations =>
                       (1 => New_Function_Decl
                            (Domain      => EW_Prog,
                             Name        => Prog_Id,
                             Binders     => Func_Why_Binders,
                             Labels      => Name_Id_Sets.Empty_Set,
                             Return_Type => EW_Unit_Type,
                             Effects     => Effects,
                             Pre         => False_Pred,
                             Post        => False_Pred))));
            end if;

            if Has_Contracts (E, Name_Refined_Post) then
               Emit
                 (File.Cur_Theory,
                  New_Namespace_Declaration
                    (Name    => NID (To_String (WNE_Refine_Module)),
                     Declarations =>
                       (1 => New_Function_Decl
                            (Domain      => EW_Prog,
                             Name        => Prog_Id,
                             Binders     => Func_Why_Binders,
                             Labels      => Name_Id_Sets.Empty_Set,
                             Return_Type => EW_Unit_Type,
                             Effects     => Effects,
                             Pre         => Pre,
                             Post        => +New_And_Expr
                               (Left   => +Refined_Post,
                                Right  => +Dynamic_Prop_Effects,
                                Domain => EW_Pred)))));
            end if;
         end;
      end if;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
   end Generate_Subprogram_Program_Fun;

   -------------------
   -- Get_Logic_Arg --
   -------------------

   function Get_Logic_Arg
     (Binder      : Binder_Type;
      Ref_Allowed : Boolean) return W_Expr_Id
   is
      Id : W_Identifier_Id;
      T  : W_Expr_Id;
      C : constant Ada_Ent_To_Why.Cursor :=
        (if Present (Binder.Ada_Node) then
              Ada_Ent_To_Why.Find (Symbol_Table, Binder.Ada_Node)
         else Ada_Ent_To_Why.Find (Symbol_Table, Binder.B_Ent));
      E : Item_Type;
   begin
      pragma Assert (if Present (Binder.Ada_Node) then
                        Ada_Ent_To_Why.Has_Element (C));

      if Ada_Ent_To_Why.Has_Element (C) then

         E := Ada_Ent_To_Why.Element (C);
         T := Reconstruct_Item (E, Ref_Allowed);

         --  If the global is associated to an entity and it is in
         --  split form, then we need to reconstruct it.

         T :=
           Insert_Simple_Conversion
             (Domain   => EW_Term,
              Expr     => T,
              To       => Get_Typ (Binder.B_Name));
      else
         Id := To_Why_Id (To_String (Binder.B_Ent), Local => False);

         if Ref_Allowed then
            T := New_Deref (Right => Id,
                            Typ   => Get_Typ (Id));
         else
            T := +Id;
         end if;
      end if;

      return T;
   end Get_Logic_Arg;

   ----------------------------------------
   -- Translate_Expression_Function_Body --
   ----------------------------------------

   procedure Translate_Expression_Function_Body
     (File : in out Why_Section;
      E    : Entity_Id)
   is
      Expr_Fun_N         : constant Node_Id := Get_Expression_Function (E);
      pragma Assert (Present (Expr_Fun_N));
      Logic_Func_Binders : constant Item_Array := Compute_Binders (E, EW_Term);
      Flat_Binders       : constant Binder_Array :=
        To_Binder_Array (Logic_Func_Binders);
      Logic_Id           : constant W_Identifier_Id :=
        To_Why_Id (E, Domain => EW_Term, Local => False,
                   Selector => (if Has_Contracts (E, Name_Refined_Post)
                                then Refine
                                else Why.Inter.Standard));

      Params : Transformation_Params;
   begin

      Open_Theory (File, E_Axiom_Module (E),
                   Comment =>
                     "Module giving a program function and a defining axiom "
                       & "for the expression function "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                   & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Add_Dependencies_For_Effects (File.Cur_Theory, E);

      --  Store an appropriate value for the result identifier in Result_Name.

      Result_Name := New_Result_Ident (Type_Of_Node (Etype (E)));

      Generate_Subprogram_Program_Fun (File, E);

      Generate_Axiom_For_Post (File, E);

      --  If the entity's body is not in SPARK,
      --  or if the function does not return, do not generate axiom.

      if not Entity_Body_In_SPARK (E) or else No_Return (E) then
         Close_Theory (File,
                       Kind => Standalone_Theory);
         return;
      end if;

      Params :=
        (File        => File.File,
         Theory      => File.Cur_Theory,
         Phase       => Generate_Logic,
         Gen_Marker   => False,
         Ref_Allowed => False);

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);

      for Binder of Logic_Func_Binders loop
         declare
            A : constant Node_Id :=
              (case Binder.Kind is
                  when Regular | Prot_Self => Binder.Main.Ada_Node,
                  when others              => raise Program_Error);
         begin
            pragma Assert (Present (A) or else Binder.Kind = Regular);

            if Present (A) then
               Ada_Ent_To_Why.Insert (Symbol_Table,
                                      Unique_Entity (A),
                                      Binder);
            elsif Binder.Main.B_Ent /= Null_Entity_Name then

               --  if there is no Ada_Node, this in a binder generated from
               --  an effect; we add the parameter in the name map using its
               --  unique name

               Ada_Ent_To_Why.Insert
                 (Symbol_Table,
                  Binder.Main.B_Ent,
                  Binder);
            end if;
         end;
      end loop;

      --  Given an expression function F with expression E, define an axiom
      --  that states that: "for all <args> => F(<args>) = E".
      --  There is no need to use the precondition here, as the above axiom
      --  is always sound.

      if Is_Standard_Boolean_Type (Etype (E)) then
         Emit
           (File.Cur_Theory,
            New_Defining_Bool_Axiom
              (Ada_Node => E,
               Name     => Logic_Id,
               Binders  => Flat_Binders,
               Def      => +Transform_Expr (Expression (Expr_Fun_N),
                                            EW_Pred,
                                            Params)));

      else
         --  For scalar types which are not modeled as their representation
         --  type in Why, using instead this representation type
         --  facilitate the job of automatic provers. As it is potentially
         --  incorrect if there can be a runtime error in the expression
         --  function body, it should not be done if the function may be
         --  recursive.
         --  For example for:

         --    function F return Natural is (Largest_Int + 1);

         --  we should *not* generate the incorrect axiom:

         --    axiom f__def:
         --      forall x:natural. to_int(f x) = to_int(largest_int) + 1

         --  but the correct one:

         --    axiom f__def:
         --      forall x:natural. f x = of_int (to_int(largest_int) + 1)

         if not Is_Non_Recursive_Subprogram (E)
           or else not Has_Scalar_Type (Etype (E))
           or else Use_Split_Form_For_Type (Etype (E))
         then
            declare
               Ty_Ent  : constant Entity_Id := Etype (E);
               Equ_Ty  : constant W_Type_Id := Type_Of_Node (Ty_Ent);
               Guard   : constant W_Pred_Id :=
                 Compute_Guard_Formula (Logic_Func_Binders);
            begin
               Emit
                 (File.Cur_Theory,
                  New_Defining_Axiom
                    (Ada_Node    => E,
                     Name        => Logic_Id,
                     Binders     => Flat_Binders,
                     Pre         => Guard,
                     Def         =>
                       +Transform_Expr
                       (Expression (Expr_Fun_N),
                        Expected_Type => Equ_Ty,
                        Domain        => EW_Term,
                        Params        => Params)));
            end;
         else
            declare
               --  Here we should use the precondition as the axiom could only
               --  be sound in its context.

               Ty_Ent  : constant Entity_Id := Etype (E);
               Equ_Ty  : constant W_Type_Id := Base_Why_Type (Ty_Ent);
               Guard   : constant W_Pred_Id :=
                 Compute_Guard_Formula (Logic_Func_Binders);
               Pre     : constant W_Pred_Id :=
                 +Compute_Spec (Params, E, Name_Precondition, EW_Pred);
            begin
               Emit
                 (File.Cur_Theory,
                  New_Guarded_Axiom
                    (Ada_Node => Empty,
                     Name     => NID (Short_Name (E) & "__" & Def_Axiom),
                     Binders  => Flat_Binders,
                     Triggers =>
                       New_Triggers
                         (Triggers =>
                              (1 => New_Trigger
                                 (Terms =>
                                    (1 => New_Call
                                         (Domain  => EW_Term,
                                          Name    => Logic_Id,
                                          Binders => Flat_Binders))))),
                     Pre      =>
                       +New_And_Expr (Left   => +Guard,
                                      Right  => +Pre,
                                      Domain => EW_Pred),
                     Def      =>
                       New_Call
                         (Name => Why_Eq,
                          Args => (Insert_Simple_Conversion
                                   (Domain         => EW_Term,
                                    Expr           => +New_Call
                                      (Name    => Logic_Id,
                                       Domain  => EW_Term,
                                       Binders => Flat_Binders,
                                       Typ     => Type_Of_Node (Ty_Ent)),
                                    To             => Equ_Ty),
                                   +Transform_Expr
                                     (Expression (Expr_Fun_N),
                                      Expected_Type => Equ_Ty,
                                      Domain        => EW_Term,
                                      Params        => Params)),
                          Typ  => EW_Bool_Type)));
            end;
         end if;
      end if;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

      --  No filtering is necessary here, as the theory should on the contrary
      --  use the previously defined theory for the function declaration. Pass
      --  in the defined entity E so that the graph of dependencies between
      --  expression functions can be built.
      --  Attach the newly created theory as a completion of the existing one.

      Close_Theory (File,
                    Kind => Axiom_Theory,
                    Defined_Entity => E);
   end Translate_Expression_Function_Body;

   -------------------------------
   -- Translate_Subprogram_Spec --
   -------------------------------

   procedure Translate_Subprogram_Spec
     (File : in out Why_Section;
      E    : Entity_Id)
   is
      Logic_Func_Binders : constant Item_Array := Compute_Binders (E, EW_Term);
      Why_Type     : W_Type_Id := Why_Empty;
   begin
      Open_Theory (File, E_Module (E),
                   Comment =>
                     "Module for possibly declaring "
                       & "a logic function for "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      if Ekind (E) = E_Function then
         Why_Type := Type_Of_Node (Etype (E));

         declare
            Logic_Why_Binders : constant Binder_Array :=
              To_Binder_Array (Logic_Func_Binders);
            Logic_Id          : constant W_Identifier_Id :=
              To_Why_Id (E, Domain => EW_Term, Local => True);
         begin
            --  Generate a logic function

            Add_Dependencies_For_Effects (File.Cur_Theory, E);

            Emit
              (File.Cur_Theory,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => Logic_Id,
                  Binders     => Logic_Why_Binders,
                  Labels      => Name_Id_Sets.Empty_Set,
                  Return_Type => Why_Type));

            if Is_Dispatching_Operation (E) then
               Emit
                 (File.Cur_Theory,
                  New_Namespace_Declaration
                    (Name    => NID (To_String (WNE_Dispatch_Module)),
                     Declarations =>
                       (1 => New_Function_Decl
                            (Domain      => EW_Term,
                             Name        => Logic_Id,
                             Binders     => Logic_Why_Binders,
                             Labels      => Name_Id_Sets.Empty_Set,
                             Return_Type => Why_Type))));
            end if;
            if Has_Contracts (E, Name_Refined_Post) then
               Emit
                 (File.Cur_Theory,
                  New_Namespace_Declaration
                    (Name    => NID (To_String (WNE_Refine_Module)),
                     Declarations =>
                       (1 => New_Function_Decl
                            (Domain      => EW_Term,
                             Name        => Logic_Id,
                             Binders     => Logic_Why_Binders,
                             Labels      => Name_Id_Sets.Empty_Set,
                             Return_Type => Why_Type))));
            end if;
         end;

         Ada_Ent_To_Why.Insert (Symbol_Table, E, Mk_Item_Of_Entity (E));
      else
         Insert_Entity (E, To_Why_Id (E, Typ => Why_Type));
      end if;

      Close_Theory (File,
                    Kind => Definition_Theory,
                    Defined_Entity => E);
   end Translate_Subprogram_Spec;

   -------------------------------------------------
   -- Update_Symbol_Table_For_Inherited_Contracts --
   -------------------------------------------------

   procedure Update_Symbol_Table_For_Inherited_Contracts (E : Entity_Id) is

      procedure Relocate_Symbols (Overridden : Entity_Id);
      --  Relocate parameters and result from Overridden subprogram to E

      ----------------------
      -- Relocate_Symbols --
      ----------------------

      procedure Relocate_Symbols (Overridden : Entity_Id) is
         From_Params : constant List_Id :=
           Parameter_Specifications (Subprogram_Specification (Overridden));
         To_Params   : constant List_Id :=
           Parameter_Specifications (Subprogram_Specification (E));
         From_Param  : Node_Id;
         To_Param    : Node_Id;

      begin
         From_Param := First (From_Params);
         To_Param := First (To_Params);
         while Present (From_Param) loop
            declare
               From_Id : constant Entity_Id :=
                 Defining_Identifier (From_Param);
               To_Id   : constant Entity_Id :=
                 Defining_Identifier (To_Param);
            begin
               Ada_Ent_To_Why.Insert
                 (Symbol_Table,
                  From_Id,
                  Ada_Ent_To_Why.Element (Symbol_Table, To_Id));
            end;

            Next (From_Param);
            Next (To_Param);
         end loop;

         pragma Assert (No (To_Param));
      end Relocate_Symbols;

      Inherit_Subp  : constant Subprogram_List := Inherited_Subprograms (E);
      Subp_For_Pre  : Entity_Id := Empty;
      Subp_For_Post : Entity_Id := Empty;
      Contracts     : Node_Lists.List;

   begin
      --  Find the subprogram from which the precondition is inherited, if any

      for J in Inherit_Subp'Range loop
         Contracts := Find_Contracts
           (Inherit_Subp (J), Name_Precondition, Classwide => True);

         if not Contracts.Is_Empty then
            Subp_For_Pre := Inherit_Subp (J);
            exit;
         end if;
      end loop;

      --  Find the subprogram from which the postcondition is inherited, if any

      for J in Inherit_Subp'Range loop
         Contracts := Find_Contracts
           (Inherit_Subp (J), Name_Postcondition, Classwide => True);

         if not Contracts.Is_Empty then
            Subp_For_Post := Inherit_Subp (J);
            exit;
         end if;
      end loop;

      if Present (Subp_For_Pre) then
         Relocate_Symbols (Subp_For_Pre);
      end if;

      if Present (Subp_For_Post) and then Subp_For_Pre /= Subp_For_Post then
         Relocate_Symbols (Subp_For_Post);
      end if;
   end Update_Symbol_Table_For_Inherited_Contracts;

end Gnat2Why.Subprograms;
