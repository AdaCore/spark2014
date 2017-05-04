------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - B I N D E R S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2017, AdaCore                   --
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

with Flow_Refinement;        use Flow_Refinement;
with Flow_Types;             use Flow_Types;
with Flow_Utility;           use Flow_Utility;
with Gnat2Why.Util;          use Gnat2Why.Util;
with Sem_Util;               use Sem_Util;
with Sinfo;                  use Sinfo;
with Snames;                 use Snames;
with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;
with SPARK_Util;             use SPARK_Util;
with SPARK_Util.Types;       use SPARK_Util.Types;
with Why.Atree.Accessors;    use Why.Atree.Accessors;
with Why.Atree.Modules;      use Why.Atree.Modules;
with Why.Conversions;        use Why.Conversions;
with Why.Gen.Expr;           use Why.Gen.Expr;
with Why.Gen.Names;          use Why.Gen.Names;
with Why.Gen.Records;        use Why.Gen.Records;
with Why.Inter;              use Why.Inter;

package body Why.Gen.Binders is

   function New_Binders
     (Domain  : EW_Domain;
      Binders : Binder_Array)
      return W_Binder_Array;

   function New_Constant_Record_Binders
     (Domain  : EW_Domain;
      Binders : Binder_Array)
      return W_Record_Binder_Array;

   function New_Expr_Array
     (Domain  : EW_Domain;
      Binders : Binder_Array)
      return W_Expr_Array;

   ----------------------------
   -- Concurrent_Self_Binder --
   ----------------------------

   function Concurrent_Self_Binder (Ty : Entity_Id) return Binder_Type is
   begin
      return
        Binder_Type'
          (B_Name   =>
             New_Identifier
               (Name => "self__",
                Typ  => Type_Of_Node (Ty)),
           B_Ent    => Null_Entity_Name,
           Ada_Node => Ty,
           Mutable  => False);
   end Concurrent_Self_Binder;

   ----------------------------
   -- Get_Ada_Node_From_Item --
   ----------------------------

   function Get_Ada_Node_From_Item (B : Item_Type) return Node_Id is
   begin
      case B.Kind is
         when Regular
            | Concurrent_Self
         =>
            return B.Main.Ada_Node;

         when DRecord =>
            if B.Fields.Present then
               return B.Fields.Binder.Ada_Node;
            else
               return B.Discrs.Binder.Ada_Node;
            end if;

         when UCArray =>
            return B.Content.Ada_Node;

         when Func =>
            raise Program_Error;
      end case;
   end Get_Ada_Node_From_Item;

   ---------------------------
   -- Get_Args_From_Binders --
   ---------------------------

   function Get_Args_From_Binders (Binders     : Binder_Array;
                                   Ref_Allowed : Boolean)
                                   return W_Expr_Array
   is
      Args    : W_Expr_Array (1 .. Binders'Length);
      I       : Positive := 1;
   begin
      for B of Binders loop
         if Ref_Allowed and then B.Mutable then
            Args (I) := New_Deref (Right => B.B_Name,
                                   Typ   => Get_Typ (B.B_Name));
         else
            Args (I) := +B.B_Name;
         end if;
         I := I + 1;
      end loop;
      return Args;
   end Get_Args_From_Binders;

   ------------------------------
   -- Get_Args_From_Expression --
   ------------------------------

   function Get_Args_From_Expression (E           : Node_Id;
                                      Ref_Allowed : Boolean)
                                      return W_Expr_Array
   is
      Scope     : constant Flow_Scope := Get_Flow_Scope (E);
      Variables : constant Flow_Id_Sets.Set :=
        Get_Variables
          (N                    => E,
           Scope                => Scope,
           Local_Constants      => Node_Sets.Empty_Set,
           Fold_Functions       => False,
           Use_Computed_Globals => True,
           Reduced              => True);
   begin
      pragma Assert (if Is_Static_Expression (E) then Variables.Is_Empty);
      return Get_Args_From_Variables (To_Name_Set (Variables), Ref_Allowed);
   end Get_Args_From_Expression;

   -----------------------------
   -- Get_Args_From_Variables --
   -----------------------------

   function Get_Args_From_Variables (Variables   : Name_Sets.Set;
                                     Ref_Allowed : Boolean)
                                     return W_Expr_Array
   is
      Items   : constant Item_Array := Get_Binders_From_Variables (Variables);
      Binders : constant Binder_Array := To_Binder_Array (Items);
   begin
      return Get_Args_From_Binders (Binders, Ref_Allowed);
   end Get_Args_From_Variables;

   ---------------------------------
   -- Get_Binders_From_Expression --
   ---------------------------------

   function Get_Binders_From_Expression (E       : Node_Id;
                                         Compute : Boolean := False)
                                         return Item_Array
   is
      Scope     : constant Flow_Scope := Get_Flow_Scope (E);
      Variables : constant Flow_Id_Sets.Set :=
        Get_Variables
          (N                    => E,
           Scope                => Scope,
           Local_Constants      => Node_Sets.Empty_Set,
           Fold_Functions       => False,
           Use_Computed_Globals => True,
           Reduced              => True);
   begin
      pragma Assert (if Is_Static_Expression (E) then Variables.Is_Empty);
      return Get_Binders_From_Variables (To_Name_Set (Variables), Compute);
   end Get_Binders_From_Expression;

   --------------------------------
   -- Get_Binders_From_Variables --
   --------------------------------

   function Get_Binders_From_Variables (Variables : Name_Sets.Set;
                                        Compute   : Boolean := False)
                                        return Item_Array
   is
      Binders : Item_Array (1 .. Natural (Variables.Length));
      I       : Positive := 1;
   begin
      for V of Variables loop
         declare
            Entity  : constant Entity_Id := Find_Entity (V);
            Use_Ent : constant Boolean := Present (Entity)
              and then not (Ekind (Entity) = E_Abstract_State)
              and then Entity_In_SPARK (Entity);

            C : constant Ada_Ent_To_Why.Cursor :=
              Ada_Ent_To_Why.Find (Symbol_Table, V);

         begin
            --  Do nothing if the entity is not mutable

            if Present (Entity) and then not Is_Mutable_In_Why (Entity) then
               null;

            --  If there is an existing binder for this entity use it

            elsif Ada_Ent_To_Why.Has_Element (C) then
               Binders (I) := Ada_Ent_To_Why.Element (C);
               I := I + 1;

            --  Otherwise, construct the binder

            elsif Use_Ent then

               --  If we are not allowed to construct binders, all the
               --  entities should be in the Symbol_Table.

               pragma Assert (Compute);

               Binders (I) := Mk_Item_Of_Entity (Entity);
               I := I + 1;
            else
               Binders (I) :=
                 (Regular,
                  Local => False,
                  Main  => (Ada_Node => Empty,
                            B_Name   =>
                              To_Why_Id (To_String (V), Local => False),
                            B_Ent    => V,
                            Mutable  => True));
               I := I + 1;
            end if;
         end;
      end loop;

      return Binders (1 .. I - 1);
   end Get_Binders_From_Variables;

   ----------------------------
   -- Get_Why_Type_From_Item --
   ----------------------------

   function Get_Why_Type_From_Item (B : Item_Type) return W_Type_Id is
   begin
      case B.Kind is
         when Regular
            | Concurrent_Self
         =>
            return Get_Typ (B.Main.B_Name);

         when DRecord =>
            return EW_Abstract (B.Typ);

         when UCArray =>
            return Get_Typ (B.Content.B_Name);

         when Func =>
            return Get_Typ (B.For_Logic.B_Name);
      end case;
   end Get_Why_Type_From_Item;

   -----------------------
   -- Item_Array_Length --
   -----------------------

   function Item_Array_Length
     (Arr        : Item_Array;
      Keep_Local : Boolean := True) return Natural
   is
      Count : Natural := 0;
   begin
      for Index in Arr'Range loop
         declare
            B : constant Item_Type := Arr (Index);
         begin
            case B.Kind is
               when Regular
                 | Concurrent_Self
                  =>
                  if (Keep_Local and then B.Local) or else B.Main.Mutable then
                     Count := Count + 1;
                  end if;

               when UCArray =>
                  pragma Assert (B.Content.Mutable);
                  if Keep_Local and then B.Local then
                     Count := Count + 1 + 2 * B.Dim;
                  else
                     Count := Count + 1;
                  end if;

               when DRecord =>
                  pragma Assert
                    ((B.Discrs.Present and then B.Discrs.Binder.Mutable)
                     or else
                       (B.Fields.Present
                        and then B.Fields.Binder.Mutable));

                  if B.Discrs.Present
                    and then ((Keep_Local and then B.Local)
                               or else B.Discrs.Binder.Mutable)
                  then
                     Count := Count + 1;
                  end if;

                  if B.Fields.Present
                    and then ((Keep_Local and then B.Local)
                               or else B.Fields.Binder.Mutable)
                  then
                     Count := Count + 1;
                  end if;

                  if Keep_Local and then B.Local and then B.Constr.Present then
                     Count := Count + 1;
                  end if;

                  if Keep_Local and then B.Local and then B.Tag.Present then
                     Count := Count + 1;
                  end if;

               when Func => raise Program_Error;
            end case;
         end;
      end loop;
      return Count;
   end Item_Array_Length;

   ------------------------------
   -- Localize_Variable_Parts --
   ------------------------------

   procedure Localize_Variable_Parts
     (Binders : in out Item_Array;
      Suffix  : String := "")
   is
   begin
      for B of Binders loop
         case B.Kind is
            when Regular
               | Concurrent_Self
            =>
               if B.Main.Mutable then
                  declare
                     Local_Name : constant String :=
                       (if Present (B.Main.Ada_Node)
                        then Full_Name (B.Main.Ada_Node)
                        else To_String (B.Main.B_Ent))
                       & Suffix;
                  begin
                     B.Main.B_Name :=
                       New_Identifier
                         (Ada_Node => B.Main.Ada_Node,
                          Name     => Local_Name,
                          Typ      => Get_Typ (B.Main.B_Name));
                  end;
               end if;

            when UCArray =>
               declare
                  Local_Name : constant String :=
                    Full_Name (B.Content.Ada_Node) & Suffix;
               begin
                  pragma Assert (B.Content.Mutable);
                  B.Content.B_Name :=
                    New_Identifier
                      (Ada_Node => B.Content.Ada_Node,
                       Name     => Local_Name,
                       Typ      => Get_Typ (B.Content.B_Name));
               end;

            when DRecord =>
               declare
                  Local_Name : constant String :=
                    (if B.Fields.Present
                     then Full_Name (B.Fields.Binder.Ada_Node)
                     else Full_Name (B.Discrs.Binder.Ada_Node))
                    & Suffix;
               begin
                  pragma Assert
                    ((B.Discrs.Present and then B.Discrs.Binder.Mutable)
                     or else (B.Fields.Present
                       and then B.Fields.Binder.Mutable));
                  if B.Discrs.Present and then B.Discrs.Binder.Mutable then
                     B.Discrs.Binder.B_Name :=
                       New_Identifier
                         (Ada_Node => B.Discrs.Binder.Ada_Node,
                          Name     => Local_Name & "__discrs",
                          Typ      => Get_Typ (B.Discrs.Binder.B_Name));
                  end if;
                  if B.Fields.Present and then B.Fields.Binder.Mutable then
                     B.Fields.Binder.B_Name :=
                       New_Identifier
                         (Ada_Node => B.Fields.Binder.Ada_Node,
                          Name     => Local_Name & "__fields",
                          Typ      => Get_Typ (B.Fields.Binder.B_Name));
                  end if;
               end;

            when Func => raise Program_Error;
         end case;
      end loop;
   end Localize_Variable_Parts;

   -----------------------
   -- Mk_Item_Of_Entity --
   -----------------------

   function Mk_Item_Of_Entity
     (E           : Entity_Id;
      Local       : Boolean := False;
      In_Fun_Decl : Boolean := False) return Item_Type
   is
      Use_Ty : constant Entity_Id :=
        (if not In_Fun_Decl
         --  test when it is safe to call Actual_Subtype
         and then (Ekind (E) in E_Constant                 |
                                E_Variable                 |
                                E_Generic_In_Out_Parameter
           or else Is_Formal (E))
         and then Present (Actual_Subtype (E))
         and then Entity_In_SPARK (Actual_Subtype (E))
         then Actual_Subtype (E)
         else Etype (E));
      --  If we are not in a function declaration, we use the actual subtype
      --  for the parameter if one is provided.

      Spec_Ty : constant Entity_Id :=
        (if Is_Class_Wide_Type (Use_Ty)
         then Get_Specific_Type_From_Classwide (Use_Ty)
         else Use_Ty);

      Ty : constant Entity_Id :=
        (if Is_Type (Spec_Ty) then Retysp (Spec_Ty) else Spec_Ty);

   begin
      --  For procedures, use a regular binder

      if Ekind (E) = E_Procedure then
         return (Regular,
                 False,
                 Binder_Type'
                   (B_Name   =>
                      To_Why_Id (E, Typ => Why_Empty),
                    B_Ent    => Null_Entity_Name,
                    Ada_Node => E,
                    Mutable  => False));

      --  For functions, store both the name to be used in logic and the name
      --  to be used in programs

      elsif Ekind (E) = E_Function then
         declare
            Typ : constant W_Type_Id := Type_Of_Node (Ty);
         begin
            return (Func,
                    False,
                    For_Logic => Binder_Type'
                      (B_Name   =>
                         To_Why_Id (E, Typ => Typ, Domain => EW_Term),
                       B_Ent    => Null_Entity_Name,
                       Ada_Node => E,
                       Mutable  => False),
                    For_Prog => Binder_Type'
                      (B_Name   =>
                         To_Why_Id (E, Typ => Typ, Domain => EW_Prog),
                       B_Ent    => Null_Entity_Name,
                       Ada_Node => E,
                       Mutable  => False));
         end;

      --  If E is not in SPARK, only declare an object of type __private for
      --  use in effects of program functions in Why3.

      elsif not Entity_In_SPARK (E) then
         declare
            Typ    : constant W_Type_Id := EW_Private_Type;
            Name   : constant W_Identifier_Id :=
              To_Why_Id (E => E, Typ => Typ, Local => Local);
            Binder : constant Binder_Type :=
              Binder_Type'(Ada_Node => E,
                           B_Name   => Name,
                           B_Ent    => Null_Entity_Name,
                           Mutable  => True);
         begin
            return (Regular, Local, Binder);
         end;

      --  If E is in SPARK, decide whether it should be split into multiple
      --  objects in Why3 or not.

      elsif Entity_In_SPARK (Ty)
        and then Is_Array_Type (Ty)
        and then not Is_Static_Array_Type (Ty)
        and then Is_Mutable_In_Why (E)
        and then Ekind (E) /= E_Loop_Parameter
      then

         --  Binders for mutable unconstrained array parameters and objects are
         --  declared in split form to preserve the bounds through loops and
         --  procedure calls. That is:
         --    A : UCArray (Index range <>);
         --  should be translated as:
         --    a : ref __split, a__first : Index'Base, a__last : Index'Base
         --  and
         --    procedure P (A : in out UCArray);
         --  should be translated as:
         --    val p (a : ref __split, a__first : rep, a__last : rep)

         declare
            Typ    : constant W_Type_Id := EW_Split (Ty);
            Name   : constant W_Identifier_Id :=
              To_Why_Id (E => E, Typ => Typ, Local => Local);
            Binder : constant Binder_Type :=
              Binder_Type'(Ada_Node => E,
                           B_Name   => Name,
                           B_Ent    => Null_Entity_Name,
                           Mutable  => Is_Mutable_In_Why (E));
            Dim    : constant Positive := Positive (Number_Dimensions (Ty));
            Bounds : Array_Bounds;
            Index  : Node_Id := First_Index (Ty);
         begin
            for D in 1 .. Dim loop
               declare
                  Index_Typ : constant W_Type_Id :=
                    (if In_Fun_Decl
                     and then Use_Base_Type_For_Type (Etype (Index)) then
                        Base_Why_Type (Etype (Index))
                     else EW_Abstract (Base_Type (Etype (Index))));
               begin
                  Bounds (D).First :=
                    Attr_Append (Name, Attribute_First, D, Index_Typ);
                  Bounds (D).Last :=
                    Attr_Append (Name, Attribute_Last, D, Index_Typ);
                  Next_Index (Index);
               end;
            end loop;

            return (Kind    => UCArray,
                    Local   => Local,
                    Content => Binder,
                    Dim     => Dim,
                    Bounds  => Bounds);
         end;

      elsif Entity_In_SPARK (Ty)
        and then (Is_Record_Type (Ty) or else Is_Private_Type (Ty))
        and then not Is_Simple_Private_Type (Ty)
        and then Is_Mutable_In_Why (E)
        and then Ekind (E) /= E_Loop_Parameter
        and then Count_Why_Top_Level_Fields (Ty) > 0
        and then (not Full_View_Not_In_SPARK (Ty)
                  or else Get_First_Ancestor_In_SPARK (Ty) /= Ty
                  or else Count_Why_Top_Level_Fields (Ty) > 1)
                  --  Do not use split form for completely private types.
      then
         declare
            Name   : constant W_Identifier_Id :=
              To_Why_Id (E => E, Local => Local);
            --  This name does not correspond to a given declaration (thus, we
            --  don't give it a type). It is only used to prefix generic names
            --  of elements of the record.

            Result   : Item_Type :=
              (Kind   => DRecord,
               Local  => Local,
               Typ    => Ty,
               others => <>);
            Unconstr : constant Boolean :=
              not Is_Constrained (Ty) and then
              Has_Defaulted_Discriminants (Ty);
         begin
            if Count_Why_Regular_Fields (Ty) > 0 then
               Result.Fields :=
                 (Present => True,
                  Binder  =>
                    Binder_Type'(Ada_Node => E,
                                 B_Name   =>
                                   Field_Append
                                     (Base => Name,
                                      Typ  =>
                                        Field_Type_For_Fields (Ty)),
                                 B_Ent    => Null_Entity_Name,
                                 Mutable  => True));
            end if;

            if Count_Discriminants (Ty) > 0 then
               Result.Discrs :=
                 (Present => True,
                  Binder  =>
                    Binder_Type'(Ada_Node => E,
                                 B_Name   =>
                                   Discr_Append
                                     (Base => Name,
                                      Typ  =>
                                        Field_Type_For_Discriminants (Ty)),
                                 B_Ent    => Null_Entity_Name,
                                 Mutable  => Unconstr));
            end if;

            if Has_Defaulted_Discriminants (Ty) then
               Result.Constr :=
                 (Present => True,
                  Id      =>
                    Attr_Append (Base     => Name,
                                 A        => Attribute_Constrained,
                                 Count    => 1,
                                 Typ      => EW_Bool_Type));
            end if;

            if Is_Tagged_Type (Ty) then
               Result.Tag :=
                 (Present => True,
                  Id      =>
                    Attr_Append (Base     => Name,
                                 A        => Attribute_Tag,
                                 Count    => 1,
                                 Typ      => EW_Int_Type));
            end if;

            return Result;
         end;

      else
         declare
            Use_Ent : constant Boolean :=
              not (Ekind (E) = E_Abstract_State)
              and then Entity_In_SPARK (E);
            --  For state abstractions pretend there is no Entity
            Typ    : constant W_Type_Id :=
              (if Ekind (E) = E_Abstract_State then
                 EW_Private_Type

               --  For loop parameters, we use a split type instead of the
               --  base type in the case where the data might require range
               --  checking. Otherwise we use the Why3 base type.

               elsif Ekind (E) = E_Loop_Parameter then
                 (if Use_Base_Type_For_Type (Ty) then
                    EW_Split (Ty)
                  else
                    Base_Why_Type_No_Bool (Ty))

               --  For function parameters, we also use a split type in the
               --  same cases.

               elsif In_Fun_Decl and then Use_Why_Base_Type (E) then
                  EW_Split (Ty)

               --  Otherwise we use Why3 representation for the type

               else Type_Of_Node (Ty));

            Name   : constant W_Identifier_Id :=
              To_Why_Id (E => E, Typ => Typ, Local => Local);
            Binder : constant Binder_Type :=
              Binder_Type'(Ada_Node => (if Use_Ent then E else Empty),
                           B_Name   => Name,
                           B_Ent    =>
                             (if Use_Ent then Null_Entity_Name
                              else To_Entity_Name (E)),
                           Mutable  => Is_Mutable_In_Why (E));
         begin
            return (Regular, Local, Binder);
         end;
      end if;
   end Mk_Item_Of_Entity;

   ---------------------------------
   -- New_Constant_Record_Binders --
   ---------------------------------

   function New_Constant_Record_Binders
     (Domain  : EW_Domain;
      Binders : Binder_Array)
      return W_Record_Binder_Array
   is

      function New_Arg_Type
        (Binder : Binder_Type)
         return W_Type_Id;

      ------------------
      -- New_Arg_Type --
      ------------------

      function New_Arg_Type
        (Binder : Binder_Type)
         return W_Type_Id is
      begin
         if Domain = EW_Prog and then Binder.Mutable then
            return New_Ref_Type (Ty => Get_Type (+Binder.B_Name));
         else
            return Get_Type (+Binder.B_Name);
         end if;
      end New_Arg_Type;

      Result : W_Record_Binder_Array (Binders'Range);

   --  Start of processing for New_Constant_Record_Binders

   begin
      for B in Binders'Range loop
         Result (B) := New_Record_Binder
           (Ada_Node   => Binders (B).Ada_Node,
            Domain     => Domain,
            Name       => Binders (B).B_Name,
            Labels     =>
              (if not Present (Binders (B).Ada_Node) or else
                  not Is_Floating_Point_Type (Etype (Binders (B).Ada_Node))
               then Get_Model_Trace_Label
                 (E               => Binders (B).Ada_Node,
                  Is_Record_Field => True)
               else Name_Id_Sets.Empty_Set),
            Arg_Type   => New_Arg_Type (Binders (B)),
            Is_Mutable => Binders (B).Mutable);
      end loop;

      return Result;
   end New_Constant_Record_Binders;

   -----------------
   -- New_Binders --
   -----------------

   function New_Binders
     (Anonymous_Binders : W_Type_Array)
      return Binder_Array
   is
      Result : Binder_Array (Anonymous_Binders'Range);
      N      : Character := 'a';
   begin
      for J in Anonymous_Binders'Range loop
         Result (J) :=
           (B_Name =>
              New_Identifier (Name => "dummy__" & N,
                              Typ => Anonymous_Binders (J)),
            others => <>);
         N := Character'Succ (N);
      end loop;

      return Result;
   end New_Binders;

   ------------------------
   -- New_Defining_Axiom --
   ------------------------

   function New_Defining_Axiom
     (Ada_Node : Node_Id := Empty;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array;
      Pre      : W_Pred_OId := Why_Empty;
      Def      : W_Term_Id)
      return W_Declaration_Id
   is
      Left       : constant W_Term_Id := +New_Call (Domain  => EW_Term,
                                                    Name    => Name,
                                                    Binders => Binders);
      Equality   : W_Pred_Id;
      Node_Name  : constant String :=
        (Get_Name_String (Get_Symbol (Get_Name (Name))));
      Axiom_Name : constant String := (if Node_Name /= ""
                                       then Node_Name & "__"
                                       else "") & Def_Axiom;
   begin
      Equality :=
        New_Call
          (Name => Why_Eq,
           Args => (+Left, +Def),
           Typ  => EW_Bool_Type);
      return New_Guarded_Axiom
        (Ada_Node => Ada_Node,
         Name     => NID (Axiom_Name),
         Binders  => Binders,
         Triggers => New_Triggers (Triggers =>
                          (1 => New_Trigger (Terms => (1 => +Left)))),
         Pre      => Pre,
         Def      => Equality);
   end New_Defining_Axiom;

   -----------------------------
   -- New_Defining_Bool_Axiom --
   -----------------------------

   function New_Defining_Bool_Axiom
     (Ada_Node : Node_Id := Empty;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array;
      Pre      : W_Pred_Id := Why_Empty;
      Def      : W_Pred_Id)
      return W_Declaration_Id
   is
      Left     : constant W_Term_Id :=
                   +New_Call
                     (Domain  => EW_Term,
                      Name    => Name,
                      Binders => Binders);
      Equality : constant W_Pred_Id :=
                   New_Equal_Bool
                     (Left  => Left,
                      Right => Def);
      Axiom_Name : constant String :=
        (if Ada_Node /= Empty then Short_Name (Ada_Node) & "__"
         else "") & Def_Axiom;
   begin
      return New_Guarded_Axiom
        (Ada_Node => Ada_Node,
         Name     => NID (Axiom_Name),
         Binders  => Binders,
         Triggers => New_Triggers (Triggers =>
                          (1 => New_Trigger (Terms => (1 => +Left)))),
         Pre      => Pre,
         Def      => Equality);
   end New_Defining_Bool_Axiom;

   -----------------
   -- New_Binders --
   -----------------

   function New_Binders
     (Domain  : EW_Domain;
      Binders : Binder_Array)
      return W_Binder_Array
   is

      function New_Arg_Type
        (Binder : Binder_Type)
         return W_Type_Id;

      ------------------
      -- New_Arg_Type --
      ------------------

      function New_Arg_Type
        (Binder : Binder_Type)
         return W_Type_Id is
      begin
         if Domain = EW_Prog and then Binder.Mutable then
            return New_Ref_Type (Ty => Get_Type (+Binder.B_Name));
         else
            return Get_Type (+Binder.B_Name);
         end if;
      end New_Arg_Type;

      Result : W_Binder_Array (Binders'Range);

   --  Start of processing for New_Binders

   begin
      for B in Binders'Range loop
         Result (B) := New_Binder
                         (Ada_Node => Binders (B).Ada_Node,
                          Domain   => Domain,
                          Name     => Binders (B).B_Name,
                          Arg_Type => New_Arg_Type (Binders (B)));
      end loop;

      return Result;
   end New_Binders;

   --------------
   -- New_Call --
   --------------

   function New_Call
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array;
      Typ      : W_Type_Id := Why_Empty)
      return W_Expr_Id is
   begin
      return New_Call
        (Ada_Node => Ada_Node,
         Domain   => Domain,
         Name     => Name,
         Args     => New_Expr_Array (Domain, Binders),
         Typ      => Typ);
   end New_Call;

   -----------------------------
   -- New_Existential_Quantif --
   -----------------------------

   function New_Existential_Quantif
     (Ada_Node : Node_Id := Empty;
      Binders  : Binder_Array;
      Pred     : W_Pred_Id)
      return W_Pred_Id is
   begin
      if Binders'Length = 0 then
         return Pred;
      else
         return New_Existential_Quantif
           (Ada_Node  => Ada_Node,
            Variables => (1 => Binders (Binders'First).B_Name),
            Var_Type  => Get_Type (+Binders (Binders'First).B_Name),
            Labels    => Name_Id_Sets.Empty_Set,
            Pred      =>
              New_Existential_Quantif (Empty,
                                       Binders (Binders'First + 1
                                                .. Binders'Last),
                                       Pred));
      end if;
   end New_Existential_Quantif;

   --------------------
   -- New_Expr_Array --
   --------------------

   function New_Expr_Array
     (Domain  : EW_Domain;
      Binders : Binder_Array)
      return W_Expr_Array
   is
   begin
      if Binders'Length = 0 and then Domain = EW_Prog then
         return (1 => +Void);
      else
         return Get_Args_From_Binders (Binders, False);
      end if;
   end New_Expr_Array;

   -----------------------
   -- New_Function_Decl --
   -----------------------

   function New_Function_Decl
     (Ada_Node    : Node_Id := Empty;
      Domain      : EW_Domain;
      Name        : W_Identifier_Id;
      Binders     : Binder_Array;
      Return_Type : W_Type_Id := Why_Empty;
      Labels      : Name_Id_Set;
      Effects     : W_Effects_Id := New_Effects;
      Def         : W_Expr_Id := Why_Empty;
      Pre         : W_Pred_Id := True_Pred;
      Post        : W_Pred_Id := True_Pred)
      return W_Declaration_Id is
   begin
      return New_Function_Decl
        (Ada_Node    => Ada_Node,
         Domain      => Domain,
         Name        => Name,
         Labels      => Labels,
         Binders     => New_Binders (Domain, Binders),
         Return_Type => +Return_Type,
         Def         => Def,
         Effects     => Effects,
         Pre         => Pre,
         Post        => Post);
   end New_Function_Decl;

   function New_Function_Decl
     (Ada_Node    : Node_Id := Empty;
      Domain      : EW_Domain;
      Name        : W_Identifier_Id;
      Items       : Item_Array;
      Return_Type : W_Type_Id := Why_Empty;
      Labels      : Name_Id_Set;
      Effects     : W_Effects_Id := New_Effects;
      Def         : W_Expr_Id := Why_Empty;
      Pre         : W_Pred_Id := True_Pred;
      Post        : W_Pred_Id := True_Pred)
      return W_Declaration_Id is
      Loc_Items : Item_Array := Items;
   begin
      Localize_Variable_Parts (Loc_Items);

      return New_Function_Decl
        (Ada_Node    => Ada_Node,
         Domain      => Domain,
         Name        => Name,
         Labels      => Labels,
         Binders     => To_Binder_Array (Loc_Items),
         Return_Type => +Return_Type,
         Def         => Def,
         Effects     => Effects,
         Pre         => Pre,
         Post        => Post);
   end New_Function_Decl;

   -----------------------
   -- New_Guarded_Axiom --
   -----------------------

   function New_Guarded_Axiom
     (Ada_Node : Node_Id := Empty;
      Name     : Name_Id;
      Binders  : Binder_Array;
      Triggers : W_Triggers_OId := Why_Empty;
      Pre      : W_Pred_OId := Why_Empty;
      Def      : W_Pred_Id)
      return W_Declaration_Id
   is
      Ax_Body  : constant W_Pred_Id :=
                   (if Pre = Why_Empty then
                      Def
                    else
                      New_Connection
                        (Op    => EW_Imply,
                         Left  => +Pre,
                         Right => +Def));
   begin
      return New_Axiom
        (Ada_Node => Ada_Node,
         Name     => Name,
         Def      =>
           New_Universal_Quantif
             (Binders  => Binders,
              Triggers => Triggers,
              Pred     => Ax_Body));
   end New_Guarded_Axiom;

   ---------------------------
   -- New_Record_Definition --
   ---------------------------

   function New_Record_Definition
      (Ada_Node : Node_Id := Empty;
       Name     : W_Name_Id;
       Binders  : Binder_Array)
       return W_Declaration_Id is
   begin
      return
         New_Type_Decl
           (Ada_Node   => Ada_Node,
            Name       => Name,
            Labels     => Name_Id_Sets.Empty_Set,
            Definition =>
              New_Record_Definition
                (Fields => New_Constant_Record_Binders (EW_Pred, Binders)));
   end New_Record_Definition;

   ---------------------------
   -- New_Universal_Quantif --
   ---------------------------

   function New_Universal_Quantif
     (Ada_Node : Node_Id := Empty;
      Binders  : Binder_Array;
      Triggers : W_Triggers_OId := Why_Empty;
      Pred     : W_Pred_Id)
      return W_Pred_Id
   is
      Cnt : Natural;
      Typ : W_Type_Id;
   begin
      if Binders'Length = 0 then
         return Pred;

      elsif Binders'Length = 1 then
         return New_Universal_Quantif
           (Ada_Node  => Ada_Node,
            Variables => (1 => Binders (Binders'First).B_Name),
            Var_Type  => Get_Type (+Binders (Binders'First).B_Name),
            Labels    => Name_Id_Sets.Empty_Set,
            Triggers  => Triggers,
            Pred      => Pred);

      else
         --  Count all the binders that have the same type as the first one. We
         --  only do that when we can compare equal types using the
         --  Eq_Base_Type function, which excludes currently types which are
         --  not of kind W_Type.

         Typ := Get_Type (+(Binders (Binders'First).B_Name));

         Cnt := 0;
         for B of Binders loop
            if Eq_In_Why (Get_Type (+B.B_Name), Typ) then
               Cnt := Cnt + 1;
            end if;
         end loop;

            pragma Assert (Cnt >= 1);

         declare
            Vars          : W_Identifier_Array (1 .. Cnt);
            Other_Binders : Binder_Array (1 .. Binders'Length - Cnt);
            Vars_Cnt      : Natural;
            Others_Cnt    : Natural;
         begin
            --  Separate binders that have the same type as the first one
            --  from the remaining binders.

            Vars_Cnt   := 0;
            Others_Cnt := 0;
            Typ        := Get_Type (+Binders (Binders'First).B_Name);
            for B of Binders loop
               if Eq_In_Why (Get_Type (+B.B_Name), Typ) then
                  Vars_Cnt := Vars_Cnt + 1;
                  Vars (Vars_Cnt) := B.B_Name;
               else
                  Others_Cnt := Others_Cnt + 1;
                  Other_Binders (Others_Cnt) := B;
               end if;
            end loop;

            --  Quantify at the same time over all binders that have the
            --  same type as the first one. This avoids the generation of
            --  very deep Why3 expressions, whose traversal may lead to
            --  stack overflow. However, avoid the recursive call in the
            --  case where [Other_Binders] is empty. This makes sure that we
            --  put the trigger on the axiom.

            if Other_Binders'Length = 0 then
               return New_Universal_Quantif
                 (Ada_Node  => Ada_Node,
                  Variables => Vars,
                  Var_Type  => Typ,
                  Labels    => Name_Id_Sets.Empty_Set,
                  Triggers  => Triggers,
                  Pred      => Pred);
            else
               return New_Universal_Quantif
                 (Ada_Node  => Ada_Node,
                  Variables => Vars,
                  Var_Type  => Typ,
                  Labels    => Name_Id_Sets.Empty_Set,
                  Pred      =>
                    New_Universal_Quantif (Ada_Node => Empty,
                                           Binders  => Other_Binders,
                                           Triggers => Triggers,
                                           Pred     => Pred));
            end if;
         end;
      end if;
   end New_Universal_Quantif;

   ----------------------------------
   -- Push_Binders_To_Symbol_Table --
   ----------------------------------

   procedure Push_Binders_To_Symbol_Table (Binders : Item_Array) is
   begin
      for B of Binders loop
         declare
            Node : constant Node_Id := Get_Ada_Node_From_Item (B);
         begin
            if Present (Node) and then not Is_Type (Node) then
               Ada_Ent_To_Why.Insert (Symbol_Table,
                                      Get_Ada_Node_From_Item (B),
                                      B);
            else
               pragma Assert (B.Kind = Regular
                              and then B.Main.B_Ent /= Null_Entity_Name);

               --  If there is no Ada_Node, this is a binder generated
               --  from an effect; we add the parameter in the name
               --  map using its unique name.

               Ada_Ent_To_Why.Insert
                 (Symbol_Table,
                  B.Main.B_Ent,
                  B);
            end if;
         end;
      end loop;
   end Push_Binders_To_Symbol_Table;

   ----------------------
   -- Reconstruct_Item --
   ----------------------

   function Reconstruct_Item
     (E           : Item_Type;
      Ref_Allowed : Boolean := True) return W_Expr_Id
   is
      T           : W_Expr_Id;
      Needs_Deref : Boolean := False;
   begin
      case E.Kind is
         when Func => raise Program_Error;

         when Regular
            | Concurrent_Self
         =>
            T := +E.Main.B_Name;
            Needs_Deref := E.Main.Mutable;

         when UCArray =>
            T := +E.Content.B_Name;
            Needs_Deref := E.Content.Mutable;

         when DRecord =>
            T := Record_From_Split_Form (E, Ref_Allowed);
      end case;

      if Ref_Allowed and then Needs_Deref then
         T := New_Deref (Ada_Node => Get_Ada_Node (+T),
                         Right    => +T,
                         Typ      => Get_Type (T));
      end if;

      return T;
   end Reconstruct_Item;

   ---------------------
   -- To_Binder_Array --
   ---------------------

   function To_Binder_Array
     (A          : Item_Array;
      Keep_Local : Boolean := True) return Binder_Array
   is
      Result : Binder_Array (1 .. Item_Array_Length (A, Keep_Local));
      Count  : Natural := 1;
   begin
      for Index in A'Range loop
         declare
            Cur : Item_Type renames A (Index);
         begin
            case Cur.Kind is
               when Regular
                  | Concurrent_Self
               =>
                  if (Keep_Local and then Cur.Local)
                    or else Cur.Main.Mutable
                  then
                     Result (Count) := Cur.Main;
                     Count := Count + 1;
                  end if;

               when UCArray =>
                  Result (Count) := Cur.Content;
                  Count := Count + 1;

                  if Keep_Local and then Cur.Local then
                     for Dim_Index in 1 .. Cur.Dim loop
                        Result (Count) :=
                          (B_Name => Cur.Bounds (Dim_Index).First,
                           others => <>);
                        Result (Count + 1) :=
                          (B_Name => Cur.Bounds (Dim_Index).Last,
                           others => <>);
                        Count := Count + 2;
                     end loop;
                  end if;

               when DRecord =>
                  if Cur.Fields.Present
                    and then ((Keep_Local and then Cur.Local)
                               or else Cur.Fields.Binder.Mutable)
                  then
                     Result (Count) := Cur.Fields.Binder;
                     Count := Count + 1;
                  end if;
                  if Cur.Discrs.Present
                    and then ((Keep_Local and then Cur.Local)
                               or else Cur.Discrs.Binder.Mutable)
                  then
                     Result (Count) := Cur.Discrs.Binder;
                     Count := Count + 1;
                  end if;
                  if Keep_Local
                    and then Cur.Local
                    and then Cur.Constr.Present
                  then
                     Result (Count) :=
                       (B_Name => Cur.Constr.Id,
                        others => <>);
                     Count := Count + 1;
                  end if;
                  if Keep_Local
                    and then Cur.Local
                    and then Cur.Tag.Present
                  then
                     Result (Count) :=
                       (B_Name => Cur.Tag.Id,
                        others => <>);
                     Count := Count + 1;
                  end if;

               when Func =>
                  raise Program_Error;
            end case;
         end;
      end loop;
      pragma Assert (Count = Result'Last + 1);
      return Result;
   end To_Binder_Array;

   ----------------
   -- Unit_Param --
   ----------------

   function Unit_Param return Binder_Type is
   begin
      return
        (B_Name   =>
           New_Identifier (Name => "__void_param", Typ => EW_Unit_Type),
         B_Ent    => Null_Entity_Name,
         Mutable  => False,
         Ada_Node => Empty);
   end Unit_Param;

end Why.Gen.Binders;
