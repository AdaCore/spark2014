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

with GNAT.Source_Info;

with Atree;                  use Atree;
with Einfo;                  use Einfo;
with Errout;                 use Errout;
with Namet;                  use Namet;
with Nlists;                 use Nlists;
with Sem_Disp;               use Sem_Disp;
with Sem_Util;               use Sem_Util;
with Sinfo;                  use Sinfo;
with Sinput;                 use Sinput;
with Snames;                 use Snames;
with Stand;                  use Stand;
with Uintp;                  use Uintp;
with VC_Kinds;               use VC_Kinds;

with Common_Containers;      use Common_Containers;

with SPARK_Definition;       use SPARK_Definition;
with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;
with SPARK_Util;             use SPARK_Util;

with Flow_Tree_Utility;      use Flow_Tree_Utility;
with Flow_Types;             use Flow_Types;
with Flow_Utility;           use Flow_Utility;

with Why;                    use Why;
with Why.Atree.Accessors;    use Why.Atree.Accessors;
with Why.Atree.Builders;     use Why.Atree.Builders;
with Why.Atree.Modules;      use Why.Atree.Modules;
with Why.Atree.Mutators;     use Why.Atree.Mutators;
with Why.Conversions;        use Why.Conversions;
with Why.Gen.Decl;           use Why.Gen.Decl;
with Why.Gen.Expr;           use Why.Gen.Expr;
with Why.Gen.Names;          use Why.Gen.Names;
with Why.Gen.Preds;          use Why.Gen.Preds;
with Why.Gen.Progs;          use Why.Gen.Progs;
with Why.Gen.Records;        use Why.Gen.Records;
with Why.Inter;              use Why.Inter;
with Why.Types;              use Why.Types;

with Gnat2Why.Decls;         use Gnat2Why.Decls;
with Gnat2Why.Expr;          use Gnat2Why.Expr;
with Gnat2Why.Nodes;         use Gnat2Why.Nodes;

package body Gnat2Why.Subprograms is

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Assign_Bounds_For_Dynamic_Types
     (Params    :        Transformation_Params;
      Scope     :        Entity_Id;
      Assume    : in out W_Prog_Id;
      Dyn_Types : in out Node_Sets.Set;
      Objects   : in out Node_Sets.Set);
   --  For each element of Dyn_Types not declared in Scope, add to Assume an
   --  updates of the corresponding bounds. If a dynamic type is a subtype or a
   --  derived type of a dynamic type, this type is added to Dyn_Types.

   procedure Assume_Dynamic_Property_For_Objects
     (Assume  : in out W_Prog_Id;
      Objects :        Node_Sets.Set;
      Scope   :        Entity_Id);
   --  For each element of Objects, add to Assume an
   --  assumption of its dynamic property.

   procedure Collect_Objects (W : Why_Node_Id; Result : in out Node_Sets.Set);
   --  Given a Why node, collects the set of external objects that are
   --  referenced in this node.

   procedure Collect_Dynamic_Types
     (W : Why_Node_Id; Result : in out Node_Sets.Set);
   --  Given a Why node, collects the set of external dynamic types
   --  that are referenced in this node.
   --  For now, it only collects types that are either unconstrained arrays or
   --  dynamic discrete.

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
   --  if any

   procedure Generate_Subprogram_Program_Fun
     (File : Why_Section;
      E    : Entity_Id);
   --  Generate a why program function for E

   procedure Generate_Axiom_For_Post
     (File : Why_Section;
      E    : Entity_Id);
   --  Generate an axiom stating the postcondition of a Subprogram

   ----------------------------------
   -- Add_Dependencies_For_Effects --
   ----------------------------------

   procedure Add_Dependencies_For_Effects
     (T : W_Theory_Declaration_Id;
      E : Entity_Id)
   is
      Read_Ids    : Flow_Types.Flow_Id_Sets.Set;
      Write_Ids   : Flow_Types.Flow_Id_Sets.Set;
      Read_Names  : Name_Set.Set;
      Write_Names : Name_Set.Set;
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

   -------------------------------------
   -- Assume_Bounds_For_Dynamic_Types --
   -------------------------------------

   procedure Assign_Bounds_For_Dynamic_Types
     (Params    :        Transformation_Params;
      Scope     :        Entity_Id;
      Assume    : in out W_Prog_Id;
      Dyn_Types : in out Node_Sets.Set;
      Objects   : in out Node_Sets.Set) is

      procedure Assume_Constraints_For_Type (Ty : Entity_Id);
      --  Calls itself recursively on the parent type used in Ty's declaration
      --  Adds affectations to the bounds of Ty to Assume
      --  Collects objects and types from bounds of Ty

      Input_Set : Node_Sets.Set;

      procedure Assume_Constraints_For_Type (Ty : Entity_Id) is
      begin
         if Type_Is_Modeled_As_Base (Ty)
           and then not Dyn_Types.Contains (Ty)
         then
            declare
               --  Type used in the declaration of Ty
               Base : constant Node_Id :=
                 (if Is_Itype (Ty) and then not Itype_Has_Declaration (Ty) then
                       Etype (Ty)
                  elsif Nkind (Parent (Ty)) = N_Subtype_Declaration then
                       Etype (Subtype_Mark (Subtype_Indication (Parent (Ty))))
                  else Etype (Subtype_Mark
                    (Subtype_Indication (Type_Definition (Parent (Ty))))));
            begin

               --  The constraints for Ty's parent type should be assumed
               --  before the constraints for Ty

               Assume_Constraints_For_Type (Base);

               --  No need to assume anything if Ty is declared in Subp

               if Get_Enclosing_Unit (Ty) = Scope then
                  return;
               end if;

               --  Do not assume the bounds of a type that depends on a
               --  discriminant.
               --  ??? are there other cases ?

               if Depends_On_Discriminant (Get_Range (Ty))
               then
                  return;
               end if;

               declare
                  Rng       : constant Node_Id := Get_Range (Ty);
                  Low_Expr  : constant W_Term_Id :=
                    +Transform_Expr (Low_Bound (Rng), Base_Why_Type (Ty),
                                     EW_Term, Params);
                  High_Expr : constant W_Term_Id :=
                    +Transform_Expr (High_Bound (Rng), Base_Why_Type (Ty),
                                     EW_Term, Params);
                  New_Types : Node_Sets.Set;
               begin

                  --  Assuming the value of Ty's bounds

                  Assume := Sequence (Left  => Assume,
                                      Right => Assume_Of_Scalar_Subtype
                                        (Params   => Params,
                                         N        => Ty,
                                         Base     => Base,
                                         Do_Check => False));

                  --  Add Ty to the set of already handled types

                  Dyn_Types.Include (Ty);

                  --  Extend Objects with objects that appear in Rng and
                  --  Dyn_Types with their types

                  Collect_Objects (+Low_Expr, Objects);
                  Collect_Objects (+High_Expr, Objects);

                  Collect_Dynamic_Types (+Low_Expr, New_Types);
                  Collect_Dynamic_Types (+High_Expr, New_Types);

                  for E of New_Types loop
                     Assume_Constraints_For_Type (E);
                  end loop;
               end;
            end;
         end if;
      end Assume_Constraints_For_Type;

   begin
      Node_Sets.Move (Input_Set, Dyn_Types);

      --  Add affectations to the ranges of elements of Dyn_Types to Assume

      for E of Input_Set loop
         Assume_Constraints_For_Type (E);
      end loop;
   end Assign_Bounds_For_Dynamic_Types;

   -----------------------------------------
   -- Assume_Dynamic_Property_For_Objects --
   -----------------------------------------

   procedure Assume_Dynamic_Property_For_Objects
     (Assume  : in out W_Prog_Id;
      Objects :        Node_Sets.Set;
      Scope   :        Entity_Id) is
   begin
      for Obj of Objects loop

         --  No need to assume anything if Obj is a local object of the
         --  subprogram.

         if not Ada_Ent_To_Why.Has_Element (Symbol_Table, Obj)
           or else (Get_Enclosing_Unit (Obj) = Scope
                    and then not (Ekind (Obj) in E_In_Parameter
                                    | E_In_Out_Parameter | E_Out_Parameter))
         then
            null;
         elsif Is_Mutable_In_Why (Obj) then
            declare
               Binder : constant Item_Type :=
                 Ada_Ent_To_Why.Element (Symbol_Table, Obj);
               Expr   : constant W_Expr_Id :=
                 (case Binder.Kind is
                     when Regular => New_Deref
                    (Ada_Node => Obj,
                     Right    => Binder.Main.B_Name,
                     Typ      => Get_Typ (Binder.Main.B_Name)),
                     when UCArray => New_Deref
                    (Ada_Node => Obj,
                     Right    => Binder.Content.B_Name,
                     Typ      => Get_Typ (Binder.Content.B_Name)),
                     when DRecord => Record_From_Split_Form (Binder, True),
                     when Func    => raise Program_Error);
            begin

               Assume :=
                 Sequence ((1 => Assume,
                            2 => Assume_Dynamic_Property
                              (Expr, Etype (Obj), False)));
            end;
         else
            Assume :=
              Sequence ((1 => Assume,
                         2 => Assume_Dynamic_Property
                           (+To_Why_Id
                              (E => Obj,
                               Typ => Why_Type_Of_Entity (Obj)),
                            Etype (Obj), False)));
         end if;
      end loop;
   end Assume_Dynamic_Property_For_Objects;

   ---------------------------
   -- Collect_Dynamic_Types --
   ---------------------------

   procedure Collect_Dynamic_Types (W      :     Why_Node_Id;
                                    Result : in out Node_Sets.Set) is

      procedure Include (Ty : Entity_Id);
      --  Collects dynamic discrete types relevant for Ty
      --  If Ty is a dynamic discrete type, add it to Result.
      --  If Ty is an unconstrained array type, add its index types if they are
      --  dynamic.

      Includes : constant Node_Sets.Set := Compute_Ada_Node_Set (W);

      procedure Include (Ty : Entity_Id) is
         Index : Node_Id;
      begin
         if Type_Is_Modeled_As_Base (Ty) then
            Result.Include (Ty);
         elsif Is_Array_Type (Ty) and then not Is_Static_Array_Type (Ty) then
            Index := First_Index (Ty);
            while Present (Index) loop
               Include (Etype (Index));
               Next_Index (Index);
            end loop;
         end if;
      end Include;
   begin
      for E of Includes loop
         if Nkind (E) in N_Entity and then Is_Type (E) then
            Include (E);
         end if;
      end loop;
   end Collect_Dynamic_Types;

   ---------------------
   -- Collect_Objects --
   ---------------------

   procedure Collect_Objects (W      :     Why_Node_Id;
                              Result : in out Node_Sets.Set) is
      Includes : constant Node_Sets.Set := Compute_Ada_Node_Set (W);
   begin
      for E of Includes loop
         if Nkind (E) in N_Entity and then Is_Object (E) then
            Result.Include (E);
         end if;
      end loop;
   end Collect_Objects;

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
        Parameter_Specifications (Get_Subprogram_Spec (E));
      Arg_Length  : constant Nat := List_Length (Ada_Binders);

   begin
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

   ---------------------
   -- Compute_Effects --
   ---------------------

   function Compute_Effects
     (E             : Entity_Id;
      Global_Params : Boolean := False) return W_Effects_Id
   is
      Read_Ids    : Flow_Types.Flow_Id_Sets.Set;
      Write_Ids   : Flow_Types.Flow_Id_Sets.Set;
      Read_Names  : Name_Set.Set;
      Write_Names : Name_Set.Set;
      Eff         : constant W_Effects_Id := New_Effects;

      Ada_Binders : constant List_Id :=
                      Parameter_Specifications (Get_Subprogram_Spec (E));

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
               declare
                  Binder : constant Item_Type :=
                    Ada_Ent_To_Why.Element (Symbol_Table, Entity);
               begin
                  case Binder.Kind is
                     when Regular =>
                        Effects_Append_To_Writes (Eff, Binder.Main.B_Name);
                     when UCArray =>
                        Effects_Append_To_Writes (Eff, Binder.Content.B_Name);
                     when DRecord =>
                        if Binder.Fields.Present then
                           Effects_Append_To_Writes
                             (Eff, Binder.Fields.Binder.B_Name);
                        end if;
                        if Binder.Discrs.Present
                          and then Binder.Discrs.Binder.Mutable
                        then
                           Effects_Append_To_Writes
                             (Eff, Binder.Discrs.Binder.B_Name);
                        end if;
                     when Func    => raise Program_Error;
                  end case;
               end;
            else
               Effects_Append_To_Writes
                 (Eff,
                  To_Why_Id (Obj => Name.all, Local => False));
            end if;
         end;
      end loop;

      --  Add all OUT and IN OUT parameters as potential writes

      declare
         Arg : Node_Id;
         Id  : Entity_Id;
         Ty  : Entity_Id;
         Ident : W_Identifier_Id;
      begin
         if Is_Non_Empty_List (Ada_Binders) then
            Arg := First (Ada_Binders);
            while Present (Arg) loop
               Id := Defining_Identifier (Arg);
               Ty := Etype (Id);
               Ty :=
                 (if Fullview_Not_In_SPARK (Ty) then Ty else MUT (Ty));

               if Ekind_In (Id, E_Out_Parameter, E_In_Out_Parameter) then

                  --  For records, we modifiy the fields if any and the
                  --  discriminants if they are mutable.

                  if Entity_In_SPARK (Ty)
                    and then Is_Record_Type (Ty)
                  then
                     if Count_Fields (Ty) > 0
                       or else Is_Tagged_Type (Ty)
                     then
                        if Global_Params then
                           Ident := Prefix
                             (W => WNE_Rec_Split_Fields,
                              M => E_Module (Id));
                        else
                           Ident := New_Identifier
                             (Name => Short_Name (Id) &
                                To_String (WNE_Rec_Split_Fields));
                        end if;
                        Effects_Append_To_Writes (Eff, Ident);
                     end if;
                     if not Is_Constrained (Ty)
                       and then Has_Defaulted_Discriminants (Ty)
                     then
                        if Global_Params then
                           Ident := Prefix
                             (W => WNE_Rec_Split_Discrs,
                              M => E_Module (Id));
                        else
                           Ident := New_Identifier
                             (Name => Short_Name (Id) &
                                To_String (WNE_Rec_Split_Discrs));
                        end if;
                        Effects_Append_To_Writes (Eff, Ident);
                     end if;
                  else
                     if Global_Params then
                        Ident :=
                          To_Why_Id (Obj => Full_Name (Id), Local => False);
                     else
                        Ident := New_Identifier (Name => Short_Name (Id));
                     end if;
                     Effects_Append_To_Writes (Eff, Ident);
                  end if;
               end if;

               Next (Arg);
            end loop;
         end if;
      end;

      for Name of Read_Names loop
         declare
            Entity : constant Entity_Id := Find_Entity (Name);
         begin

            if Present (Entity)
              and then not (Ekind (Entity) = E_Abstract_State)
              and then Entity_In_SPARK (Entity)
            then
               declare
                  Binder : constant Item_Type :=
                    Ada_Ent_To_Why.Element (Symbol_Table, Entity);
               begin
                  case Binder.Kind is
                     when Regular =>
                        Effects_Append_To_Reads (Eff, Binder.Main.B_Name);
                     when UCArray =>
                        Effects_Append_To_Reads (Eff, Binder.Content.B_Name);
                     when DRecord =>
                        if Binder.Fields.Present then
                           Effects_Append_To_Reads
                             (Eff, Binder.Fields.Binder.B_Name);
                        end if;
                        if Binder.Discrs.Present
                          and then Binder.Discrs.Binder.Mutable
                        then
                           Effects_Append_To_Reads
                             (Eff, Binder.Discrs.Binder.B_Name);
                        end if;
                     when Func    => raise Program_Error;
                  end case;
               end;
            else
               Effects_Append_To_Reads
                 (Eff,
                  To_Why_Id (Obj => Name.all, Local => False));
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
                  else New_Call (Name =>
                                     Prefix (M        => E_Module (Ty),
                                             W        => WNE_Range_Pred,
                                             Ada_Node => Ty),
                                 Args => (1 => +B.Main.B_Name)));
            begin
               Pred :=
                 +New_And_Then_Expr
                 (Domain => EW_Pred,
                  Left   => +Pred,
                  Right  => +Guard);
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
      Read_Names  : Name_Set.Set;

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
                           Typ  => EW_Abstract (Etype (Entity))),
                      B_Ent    => null,
                      Mutable  => False));
               else
                  Result (Count) :=
                    (Regular,
                     (Ada_Node => Empty,
                      B_Name   =>
                        New_Identifier
                          (Name => R.all,
                           Typ  => To_Why_Type (R.all)),
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
      Params : constant List_Id :=
                 Parameter_Specifications (Get_Subprogram_Spec (E));
      Result : Item_Array (1 .. Integer (List_Length (Params)));
      Param  : Node_Id;
      Count  : Integer;

   begin
      Param := First (Params);
      Count := 1;
      while Present (Param) loop

         --  We do not want to add a dependency to the Id entity here, so we
         --  set the ada node to empty. However, we still need the entity for
         --  the Name_Map of the translation, so we store it in the binder.

         declare
            Id   : constant Node_Id := Defining_Identifier (Param);
            Ty   : constant Entity_Id :=
              (if Fullview_Not_In_SPARK (Etype (Id)) then Etype (Id)
               else MUT (Etype (Id)));
         begin
            if Is_Record_Type (Ty)
              and then Is_Mutable_In_Why (Id)
            then

               --  Binders for mutable record parameters have to be given in
               --  split form to preserve the attributes and discriminants
               --  through procedure calls.

               declare
                  Binder   : Item_Type :=
                    (Kind   => DRecord,
                     Typ    => Ty,
                     others => <>);
                  Unconstr : constant Boolean :=
                    not Is_Constrained (Ty) and then
                    Has_Defaulted_Discriminants (Ty);
               begin
                  if Count_Fields (Ty) > 0
                    or else Is_Tagged_Type (Ty)
                  then
                     Binder.Fields :=
                       (Present => True,
                        Binder  =>
                          Binder_Type'
                            (Ada_Node => Id,
                             B_Name   =>
                               New_Identifier
                                 (Ada_Node => Id,
                                  Domain   => EW_Term,
                                  Name     => Short_Name (Id) &
                                      To_String (WNE_Rec_Split_Fields),
                                  Typ      =>
                                    Field_Type_For_Fields (Ty)),
                             B_Ent    => null,
                             Mutable  => True));
                  end if;

                  if Number_Discriminants (Ty) > 0 then
                     Binder.Discrs :=
                       (Present => True,
                        Binder  =>
                          Binder_Type'
                            (Ada_Node => Id,
                             B_Name   =>
                               New_Identifier
                                 (Ada_Node => Id,
                                  Domain   => EW_Term,
                                  Name     => Short_Name (Id) &
                                      To_String (WNE_Rec_Split_Discrs),
                                  Typ      =>
                                    Field_Type_For_Discriminants (Ty)),
                             B_Ent    => null,
                             Mutable  => Unconstr));
                  end if;

                  if Unconstr then
                     Binder.Constr :=
                       (Present => True,
                        Id      => New_Identifier
                          (Ada_Node => Id,
                           Domain   => EW_Term,
                           Name     => Short_Name (Id) & "__" &
                             To_String (WNE_Attr_Constrained),
                           Typ      => EW_Bool_Type));
                  end if;

                  if Is_Tagged_Type (Ty) then
                     Binder.Tag :=
                       (Present => True,
                        Id      => New_Identifier
                          (Ada_Node => Id,
                           Domain   => EW_Term,
                           Name     => Short_Name (Id) & "__" &
                             To_String (WNE_Attr_Tag),
                           Typ      => EW_Int_Type));
                  end if;

                  Result (Count) := Binder;
               end;
            elsif Is_Array_Type (Ty)
              and then not Is_Static_Array_Type (Ty)
              and then Is_Mutable_In_Why (Id)
            then

               --  Binders for mutable unconstrained array parameters have to
               --  be given in split form to preserve the bounds through
               --  procedure calls. That is:
               --    procedure P (A : in out UCArray);
               --  is should be translated as:
               --    val p (a : ref __split, a__first : int, a__last : int)

               declare
                  Dim    : constant Positive :=
                    Positive (Number_Dimensions (Ty));
                  Bounds : Array_Bounds;
                  Index  : Node_Id := First_Index (Ty);
                  Typ  : constant W_Type_Id := EW_Split (Ty);
                  Name : constant W_Identifier_Id :=
                    New_Identifier (Ada_Node => Id,
                                    Name     => Short_Name (Id),
                                    Typ      => Typ);
               begin
                  for I in 1 .. Dim loop
                     declare
                        Index_Typ : constant W_Type_Id :=
                          (if Use_Base_Type_For_Type (Etype (Index)) then
                                Base_Why_Type (Base_Type (Etype (Index)))
                           else EW_Abstract (Etype (Index)));
                     begin
                        Bounds (I) :=
                          (Append_Num (S        => Short_Name (Id) & "__first",
                                       Count    => I,
                                       Typ      => Index_Typ,
                                       Ada_Node => Empty),
                           Append_Num (S        => Short_Name (Id) & "__last",
                                       Count    => I,
                                       Typ      => Index_Typ,
                                       Ada_Node => Empty));
                     end;
                     Next_Index (Index);
                  end loop;

                  Result (Count) :=
                    (UCArray,
                     Content => (Ada_Node => Id,
                                 B_Name   => Name,
                                 B_Ent    => null,
                                 Mutable  => Is_Mutable_In_Why (Id)),
                     Dim    => Dim,
                     Bounds => Bounds);
               end;
            else
               declare
                  Typ  : constant W_Type_Id :=
                    (if Use_Why_Base_Type (Id) then
                          Base_Why_Type (Unique_Entity (Ty))
                     else EW_Abstract (Ty));
                  Name : constant W_Identifier_Id :=
                    New_Identifier (Ada_Node => Id,
                                    Name     => Short_Name (Id),
                                    Typ      => Typ);
               begin
                  Result (Count) :=
                    (Regular,
                     (Ada_Node => Id,
                      B_Name   => Name,
                      B_Ent    => null,
                      Mutable  => Is_Mutable_In_Why (Id)));
               end;
            end if;
            Next (Param);
            Count := Count + 1;
         end;
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
      Prag          : constant Node_Id := Get_Subprogram_Contract_Cases (E);
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
      Prag          : constant Node_Id := Get_Subprogram_Contract_Cases (E);
      Aggr          : Node_Id;
      Contract_Case : Node_Id;
      Case_Guard    : Node_Id;

      Has_Others  : Boolean := False;
      --  Set to True if there is an OTHERS guard

      Count       : W_Expr_Id := New_Integer_Constant (Value => Uint_0);
      --  Count of the guards enabled

      Result      : W_Prog_Id := New_Void;
      --  Why program for these checks

   --  Start of Compute_Contract_Cases_Entry_Checks

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
      Prag          : constant Node_Id := Get_Subprogram_Contract_Cases (E);
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

   --  Start of Compute_Contract_Cases_Exit_Checks

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
      Prag          : constant Node_Id := Get_Subprogram_Contract_Cases (E);
      Aggr          : Node_Id;
      Contract_Case : Node_Id;
      Case_Guard    : Node_Id;
      Consequence   : Node_Id;

      Result : W_Pred_Id := New_Literal (Value => EW_True);

   --  Start of Compute_Contract_Cases_Postcondition

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
      Spec_N     : constant Node_Id := Get_Package_Spec (E);
      Body_N     : constant Node_Id := Get_Package_Body (E);
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
                 Gen_Marker   => False,
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

      declare
         Used_Dyn_Types : Node_Sets.Set;
         Used_Objects   : Node_Sets.Set;
         Assume         : W_Prog_Id := New_Void;
      begin
         Collect_Dynamic_Types (W      => +Why_Body,
                                Result => Used_Dyn_Types);
         Collect_Objects (W      => +Why_Body,
                          Result => Used_Objects);

         --  Assume bounds of external dynamic types used in the program

         Assign_Bounds_For_Dynamic_Types (Params    => Params,
                                          Scope     => E,
                                          Assume    => Assume,
                                          Dyn_Types => Used_Dyn_Types,
                                          Objects   => Used_Objects);

         --  We assume that objects used in the program are in range, if
         --  they are of a dynamic type

         Assume_Dynamic_Property_For_Objects (Assume  => Assume,
                                              Objects => Used_Objects,
                                              Scope   => E);
         Why_Body :=
           Sequence (Assume, Why_Body);
      end;

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

      Inherited_Pre_Spec  : W_Pred_Id;
      Classwide_Pre_Spec  : W_Pred_Id;
      Pre_Spec            : W_Pred_Id;
      Inherited_Post_Spec : W_Pred_Id;
      Classwide_Post_Spec : W_Pred_Id;
      Post_Spec           : W_Pred_Id;

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

      Result_Name :=
        New_Identifier
             (Name => Name & "__result", Typ => EW_Abstract (Etype (E)));

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
           New_Assume_Statement (Post => Inherited_Pre_Spec);

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
           New_Assume_Statement (Post =>
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
           ((1 => Why_Body,
             2 => New_Comment (Comment =>
                               NID ("Checking that precondition is"
                                  & " implied by class-wide precondition")),
             3 => Classwide_Pre_Assume,
             4 => Pre_Check));

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
           New_Assume_Statement (Post =>
             Get_Static_Call_Contract (Params, E, Name_Precondition));

         Call_Effects := New_Havoc_Statement
           (Ada_Node => E,
            Effects  => +Compute_Effects (E, Global_Params => True));

         Post_Assume := New_Assume_Statement (Post => Post_Spec);

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

         if Is_Overriding_Subprogram (E) then
            Classwide_Post_Assume :=
              New_Assume_Statement (Post => Classwide_Post_Spec);

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
                2 => Classwide_Post_Assume,
                3 => Inherited_Post_Check));

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

      --  Declare a global variable to hold the result of a function

      if Ekind (E) = E_Function then
         Emit
           (File.Cur_Theory,
            New_Global_Ref_Declaration
              (Name     => Result_Name,
               Labels =>
                 Name_Id_Sets.To_Set
                   (NID ("""GP_Ada_Name:" & Source_Name (E) & "'Result""")),
               Ref_Type => EW_Abstract (Etype (E))));
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

      Body_N    : constant Node_Id := SPARK_Util.Get_Subprogram_Body (E);
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
      Result_Name :=
        New_Identifier
             (Name => Name & "__result", Typ => EW_Abstract (Etype (E)));
      Result_Var :=
        (if Ekind (E) = E_Function then
              New_Deref
           (Ada_Node => Body_N,
            Right    => Result_Name)
         else New_Void);

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
         Assume := Transform_Declarations_Not_From_Source
           (Declarations (Body_N));
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
         if Might_Be_Main (E) then
            Precondition :=
              New_Located_Assert
                (Ada_Node => Get_Location_For_Aspect (E, Name_Precondition),
                 Pred     => Pre,
                 Reason   => VC_Precondition_Main,
                 Kind     => EW_Assert);
         else
            Precondition := New_Assume_Statement (Post => Pre);
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
          6 => Precondition));
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
         --  has postcondition false, but the precondition is unchanged

         if No_Return (E) then
            Post := False_Pred;
         else
            Params.Gen_Marker := True;
            Post := Get_Static_Call_Contract (Params, E, Name_Postcondition);
            Params.Gen_Marker := False;
         end if;

         Post := +New_VC_Expr (Post_N, +Post, VC_Postcondition, EW_Pred);

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
                  Labels =>
                    Name_Id_Sets.To_Set
                      (NID ("""GP_Ada_Name:" & Source_Name (E) & "'Result""")),
                  Ref_Type => EW_Abstract (Etype (E))));
         end if;

         --  Translate statements in the body of the subp

         Why_Body :=
           Transform_Statements_And_Declarations
             (Statements
                (Handled_Statement_Sequence (Body_N)));

         --  Translate statements in declaration block

         Why_Body :=
           Sequence
             (Transform_Declarations_From_Source (Declarations (Body_N)),
              Why_Body);

         --  Enclose the subprogram body in a try-block, so that return
         --  statements can be translated as raising exceptions.

         declare
            Raise_Stmt : constant W_Prog_Id :=
              New_Raise
                (Ada_Node => Body_N,
                 Name     => Return_Exc);
         begin
            Why_Body :=
              New_Try_Block
                (Prog    => Sequence (Why_Body, Raise_Stmt),
                 Handler =>
                   (1 =>
                          New_Handler
                      (Name => Return_Exc,
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
                  if Is_Pragma_Check (Decl, Name_Precondition) and then
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
                 Post =>
                     +Compute_Spec (Params, E, Name_Refined_Post, EW_Pred));
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

      --  Generate assumptions for dynamic types used in the program.

      if Present (Body_N) and then Entity_Body_In_SPARK (E) then
         Assume := New_Void;

         declare
            Used_Dyn_Types : Node_Sets.Set;
            Used_Objects   : Node_Sets.Set;
         begin
            Collect_Dynamic_Types (W      => +Prog,
                                   Result => Used_Dyn_Types);
            Collect_Objects (W      => +Prog,
                             Result => Used_Objects);

            --  Assume bounds of external dynamic types used in the program

            Assign_Bounds_For_Dynamic_Types (Params    => Params,
                                             Scope     => E,
                                             Assume    => Assume,
                                             Dyn_Types => Used_Dyn_Types,
                                             Objects   => Used_Objects);

            --  We assume that objects used in the program are in range, if
            --  they are of a dynamic type

            Assume_Dynamic_Property_For_Objects (Assume  => Assume,
                                                 Objects => Used_Objects,
                                                 Scope   => E);
         end;

         Prog := Sequence
           ((1 => New_Comment
             (Comment => NID ("Assume dynamic property of params of the"
              & " subprogram"
              & (if Sloc (E) > 0 then " " & Build_Location_String (Sloc (E))
                else ""))),
             2 => Assume,
             3 => Prog));
      end if;

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

      --  We should *not* filter our own entity, it is needed for recursive
      --  calls

      Close_Theory (File,
                    Kind => VC_Generation_Theory,
                    Defined_Entity => E);
   end Generate_VCs_For_Subprogram;

   -----------------------------
   -- Get_Location_For_Aspect --
   -----------------------------

   function Get_Location_For_Aspect
     (E         : Entity_Id;
      Kind      : Name_Id;
      Classwide : Boolean := False) return Node_Id is
   begin

      --  In the case of a No_Return Subprogram, there is no real location for
      --  the postcondition; simply return the subp entity node.

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
      Refined_Post        : W_Pred_Id;
      Why_Type           : W_Type_Id := Why_Empty;
   begin

      if Ekind (E) = E_Procedure
        or else No_Return (E)
        or else not Is_Non_Recursive_Subprogram (E)
      then
         return;
      end if;

      Why_Type := EW_Abstract (Etype (E));

      --  If the function has a postcondition is not mutually recursive
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
      --  local names of the parameters, instead of the global names

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);

      for Binder of Logic_Func_Binders loop
         declare
            A : constant Node_Id :=
              (case Binder.Kind is
                  when Regular => Binder.Main.Ada_Node,
                  when others  => raise Program_Error);
            --  in parameters should not be split
         begin
            pragma Assert (Present (A) or else Binder.Kind = Regular);

            if Present (A) then
               Ada_Ent_To_Why.Insert (Symbol_Table,
                                      Unique_Entity (A),
                                      Binder);
            elsif Binder.Main.B_Ent /= null then

               --  if there is no Ada_Node, this is a binder generated
               --  from an effect; we add the parameter in the name
               --  map using its unique name

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

      --  Add to post the dynamic property of the result.

      Post :=
        +New_And_Expr
        (Left   => +Post,
         Right  => +Compute_Dynamic_Property
           (Expr     => +New_Result_Ident (Why_Type),
            Ty       => Etype (E),
            Only_Var => False),
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
         begin
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
                     Context  => +Post)));
         end Emit_Post_Axiom;

         --  beginning of processing of Generate_Axiom_For_Post

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
         Gen_Marker   => False,
         Ref_Allowed => True);

      --  We fill the map of parameters, so that in the pre and post, we use
      --  local names of the parameters, instead of the global names

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);

      for Binder of Func_Binders loop
         declare
            A : constant Node_Id :=
              (case Binder.Kind is
                  when Regular => Binder.Main.Ada_Node,
                  when UCArray => Binder.Content.Ada_Node,
                  when DRecord => (if Binder.Fields.Present then
                                        Binder.Fields.Binder.Ada_Node
                                   else Binder.Discrs.Binder.Ada_Node),
                  when Func    => raise Program_Error);
         begin

            --  If the Ada_Node is empty, it's not an interesting binder
            --  (e.g. void_param)

            if Present (A) then
               Ada_Ent_To_Why.Insert (Symbol_Table, A, Binder);
            end if;
         end;
      end loop;

      Effects := Compute_Effects (E);

      --  A procedure can be marked No_Return either to denote an error
      --  reporting subprogram, or because it is the subprogram of a main loop.

      --  For a subprogram reporting an error, the precondition at call site
      --  should be "False", so that calling it is an error.

      if No_Return (E) and then Get_Abend_Kind (E) = Abnormal_Termination then
         Pre := False_Pred;

         if Is_Dispatching_Operation (E) then
            Dispatch_Pre := False_Pred;
         end if;

      --  In other cases (including the subprogram of a main loop), the
      --  precondition is extracted from the subprogram contract.

      else
         Pre := Get_Static_Call_Contract (Params, E, Name_Precondition);

         if Is_Dispatching_Operation (E) then
            Dispatch_Pre :=
              Get_Dispatching_Contract (Params, E, Name_Precondition);
         end if;
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

         Why_Type := EW_Abstract (Etype (E));

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

            --  Each function has in its postcondition that its result is
            --  equal to the application of the corresponding logic function
            --  to the same arguments.

            Param_Post          : constant W_Pred_Id :=
              +New_And_Expr
              (Left   =>
                 New_Call
                   (Name   => Why_Eq,
                    Domain => EW_Pred,
                    Typ    => EW_Bool_Type,
                    Args   => (+New_Result_Ident (Why_Type),
                               New_Call
                                 (Domain => EW_Term,
                                  Name   => Logic_Id,
                                  Args   => Logic_Func_Args))),
               Right  =>
                 +New_And_Expr
                 (Left   =>
                      +Compute_Dynamic_Property
                    (Expr     => +New_Result_Ident (Why_Type),
                     Ty       => Etype (E),
                     Only_Var => False),
                  Right  => +Post,
                  Domain => EW_Pred),
               Domain => EW_Pred);

            Dispatch_Param_Post : W_Pred_Id;
            Refine_Param_Post   : W_Pred_Id;

         begin
            Emit
              (File.Cur_Theory,
               New_Function_Decl
                 (Domain      => EW_Prog,
                  Name        => Prog_Id,
                  Binders     => Func_Why_Binders,
                  Return_Type => EW_Abstract (Etype (E)),
                  Labels      => Name_Id_Sets.Empty_Set,
                  Pre         => Pre,
                  Post        => Param_Post));

            if Is_Dispatching_Operation (E) then
               Dispatch_Param_Post :=
                 +New_And_Expr
                 (Left   =>
                    New_Call
                      (Domain => EW_Pred,
                       Name   => Why_Eq,
                       Typ    => EW_Bool_Type,
                       Args =>
                         (+New_Result_Ident (Why_Type),
                          New_Call
                            (Domain  => EW_Term,
                             Name    => Dispatch_Logic_Id,
                             Args    => Logic_Func_Args))),
                  Right  => +Dispatch_Post,
                  Domain => EW_Pred);

               Emit
                 (File.Cur_Theory,
                  New_Namespace_Declaration
                    (Name    => NID (To_String (WNE_Dispatch_Module)),
                     Declarations =>
                       (1 => New_Function_Decl
                            (Domain      => EW_Prog,
                             Name        => Prog_Id,
                             Binders     => Func_Why_Binders,
                             Return_Type => EW_Abstract (Etype (E)),
                             Labels      => Name_Id_Sets.Empty_Set,
                             Pre         => Dispatch_Pre,
                             Post        => Dispatch_Param_Post))));
            end if;
            if Has_Contracts (E, Name_Refined_Post) then
               Refine_Param_Post :=
                 +New_And_Expr
                 (Left   =>
                    New_Call
                      (Domain => EW_Pred,
                       Name   => Why_Eq,
                       Typ    => EW_Bool_Type,
                       Args   =>
                         (1 => +New_Result_Ident (Why_Type),
                          2 =>
                            New_Call
                              (Domain  => EW_Term,
                               Name    => Refine_Logic_Id,
                               Args    => Logic_Func_Args))),
                  Right  => +Refined_Post,
                  Domain => EW_Pred);
               Emit
                 (File.Cur_Theory,
                  New_Namespace_Declaration
                    (Name    => NID (To_String (WNE_Refine_Module)),
                     Declarations =>
                       (1 => New_Function_Decl
                            (Domain      => EW_Prog,
                             Name        => Prog_Id,
                             Binders     => Func_Why_Binders,
                             Return_Type => EW_Abstract (Etype (E)),
                             Labels      => Name_Id_Sets.Empty_Set,
                             Pre         => Pre,
                             Post        => Refine_Param_Post))));
            end if;
         end;

      --  Ekind (E) = E_Procedure

      else

         --  Add to postcondition the dynamic property of mutable parameters

         for I in Func_Why_Binders'Range loop
            if Func_Why_Binders (I).Mutable then
               declare
                  Binder   : constant Binder_Type := Func_Why_Binders (I);
                  Dyn_Prop : constant W_Pred_Id :=
                    Compute_Dynamic_Property
                      (Expr     => Transform_Identifier
                         (Params   => Params,
                          Expr     => Binder.Ada_Node,
                          Ent      => Binder.Ada_Node,
                          Domain   => EW_Pred),
                       Ty       => Etype (Binder.Ada_Node),
                       Only_Var => True);
               begin
                  if Dyn_Prop /= True_Pred then
                     Post := +New_And_Expr
                       (Left   => +Post,
                        Right  => +Dyn_Prop,
                        Domain => EW_Pred);
                  end if;
               end;
            end if;
         end loop;

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
               Post        => Post));

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
                          Post        => Dispatch_Post))));
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
                          Post        => Refined_Post))));
         end if;
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

         case E.Kind is
         when Regular =>
            Id := E.Main.B_Name;

            if Ref_Allowed then
               T := New_Deref (Right => Id,
                               Typ   => Get_Typ (Id));
            else
               T := +Id;
            end if;
         when UCArray =>
            Id := E.Content.B_Name;

            if Ref_Allowed then
               T := New_Deref (Right => Id,
                               Typ   => Get_Typ (Id));
            else
               T := +Id;
            end if;

            --  If the global is associated to an entity and it is in
            --  split form, then we need to reconstruct it.

            T :=
              Insert_Simple_Conversion
                (Domain   => EW_Term,
                 Expr     => T,
                 To       => Get_Typ (Binder.B_Name));
         when DRecord =>
            T := Record_From_Split_Form (E, Ref_Allowed);
         when Func => raise Program_Error;
         end case;
      else
         Id := To_Why_Id (Binder.B_Ent.all, Local => False);

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
                             To_Why_Id (E, Domain => EW_Term, Local => False);

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
                  when Regular => Binder.Main.Ada_Node,
                  when others  => raise Program_Error);
         begin
            pragma Assert (Present (A) or else Binder.Kind = Regular);

            if Present (A) then
               Ada_Ent_To_Why.Insert (Symbol_Table,
                                      Unique_Entity (A),
                                      Binder);
            elsif Binder.Main.B_Ent /= null then

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
         declare
            --  Always use the Ada type for the equality between the function
            --  result and the translation of its expression body. Using "int"
            --  instead is tempting to facilitate the job of automatic provers,
            --  but it is potentially incorrect. For example for:

            --    function F return Natural is (Largest_Int + 1);

            --  we should *not* generate the incorrect axiom:

            --    axiom f__def:
            --      forall x:natural. to_int(x) = to_int(largest_int) + 1

            --  but the correct one:

            --    axiom f__def:
            --      forall x:natural. x = of_int (to_int(largest_int) + 1)

            Ty_Ent  : constant Entity_Id := Unique_Entity (Etype (E));
            Equ_Ty  : constant W_Type_Id := EW_Abstract (Ty_Ent);
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

      function Get_Subp_Symbol (Domain   : EW_Domain) return Binder_Type
      is
        (Binder_Type'(B_Name   =>
                        To_Why_Id (E, Typ => Why_Type, Domain => Domain),
                      B_Ent    => null,
                      Ada_Node => E,
                      Mutable  => False));

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
         Why_Type := EW_Abstract (Etype (E));

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

         Ada_Ent_To_Why.Insert
           (Symbol_Table, E,
            Item_Type'(Func,
              For_Logic => Get_Subp_Symbol (EW_Term),
              For_Prog  => Get_Subp_Symbol (EW_Prog)));
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
           Parameter_Specifications (Get_Subprogram_Spec (Overridden));
         To_Params   : constant List_Id :=
           Parameter_Specifications (Get_Subprogram_Spec (E));
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
