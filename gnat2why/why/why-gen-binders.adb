------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - B I N D E R S                       --
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

with Atree;               use Atree;
with Einfo;               use Einfo;
with Sem_Util;            use Sem_Util;
with Sinfo;               use Sinfo;
with Snames;              use Snames;

with SPARK_Util;          use SPARK_Util;

with Gnat2Why.Util;       use Gnat2Why.Util;
with Why.Atree.Modules;   use Why.Atree.Modules;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Conversions;     use Why.Conversions;
with Why.Gen.Expr;        use Why.Gen.Expr;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Records;     use Why.Gen.Records;
with Why.Inter;           use Why.Inter;

package body Why.Gen.Binders is

   function New_Binders
     (Domain  : EW_Domain;
      Binders : Binder_Array)
     return W_Binder_Array;

   function New_Expr_Array
     (Domain  : EW_Domain;
      Binders : Binder_Array)
      return W_Expr_Array;

   ----------------------------
   -- Get_Ada_Node_From_Item --
   ----------------------------

   function Get_Ada_Node_From_Item (B : Item_Type) return Node_Id is
   begin
      case B.Kind is
         when Regular =>
            return B.Main.Ada_Node;
         when DRecord =>
            if B.Fields.Present then
               return B.Fields.Binder.Ada_Node;
            else
               return B.Discrs.Binder.Ada_Node;
            end if;
         when UCArray =>
            return B.Content.Ada_Node;
         when Func    =>
            raise Program_Error;
      end case;
   end Get_Ada_Node_From_Item;

   ----------------------------
   -- Get_Why_Type_From_Item --
   ----------------------------

   function Get_Why_Type_From_Item (B : Item_Type) return W_Type_Id is
   begin
      case B.Kind is
         when Regular =>
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

   function Item_Array_Length (Arr : Item_Array) return Natural is
      Count : Natural := 0;
   begin
      for Index in Arr'Range loop
         case Arr (Index).Kind is
            when Regular => Count := Count + 1;
            when UCArray => Count := Count + 1 + 2 * Arr (Index).Dim;
            when DRecord =>
               if Arr (Index).Fields.Present then
                  Count := Count + 1;
               end if;
               if Arr (Index).Discrs.Present then
                  Count := Count + 1;
               end if;
               if Arr (Index).Constr.Present then
                  Count := Count + 1;
               end if;
               if Arr (Index).Tag.Present then
                  Count := Count + 1;
               end if;
            when Func    => raise Program_Error;
         end case;
      end loop;
      return Count;
   end Item_Array_Length;

   -------------------------
   -- Mk_Item_From_Entity --
   -------------------------

   function Mk_Item_Of_Entity
     (E           : Entity_Id;
      Local       : Boolean := False;
      In_Fun_Decl : Boolean := False)
      return Item_Type
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

      Ty     : constant Entity_Id :=
        (if Ekind (Use_Ty) in Type_Kind then Retysp (Use_Ty) else Use_Ty);

   begin
      if Entity_In_SPARK (Ty)
        and then Is_Array_Type (Ty)
        and then not Is_Static_Array_Type (Ty)
        and then Is_Mutable_In_Why (E)
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
                           B_Ent    => null,
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
                    Content => Binder,
                    Dim     => Dim,
                    Bounds  => Bounds);
         end;
      elsif Entity_In_SPARK (Ty)
        and then (Is_Record_Type (Ty) or else Is_Private_Type (Ty))
        and then Is_Mutable_In_Why (E)
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
                                 B_Ent    => null,
                                 Mutable  => True));
            end if;

            if Has_Discriminants (Ty) then
               Result.Discrs :=
                 (Present => True,
                  Binder  =>
                    Binder_Type'(Ada_Node => E,
                                 B_Name   =>
                                   Discr_Append
                                     (Base => Name,
                                      Typ  =>
                                        Field_Type_For_Discriminants (Ty)),
                                 B_Ent    => null,
                                 Mutable  => Unconstr));
            end if;

            if Unconstr then
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
            Typ    : constant W_Type_Id :=
              (if Ekind (E) = E_Abstract_State then EW_Private_Type
               elsif Ekind (E) = E_Loop_Parameter then
                    Base_Why_Type_No_Bool (Ty)
               elsif In_Fun_Decl and then Use_Why_Base_Type (E) then
                    Base_Why_Type (Ty)
               else Type_Of_Node (Ty));
            --  For loop parameters, we use the Why3 representation type.

            Name   : constant W_Identifier_Id :=
              To_Why_Id (E => E, Typ => Typ, Local => Local);
            Binder : constant Binder_Type :=
              Binder_Type'(Ada_Node => E,
                           B_Name   => Name,
                           B_Ent    => null,
                           Mutable  => Is_Mutable_In_Why (E));
         begin
            return (Regular, Binder);
         end;
      end if;
   end Mk_Item_Of_Entity;

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
     (Ada_Node    : Node_Id := Empty;
      Name        : W_Identifier_Id;
      Binders     : Binder_Array;
      Pre         : W_Pred_OId := Why_Empty;
      Def         : W_Term_Id)
     return W_Declaration_Id
   is
      Left : constant W_Term_Id := +New_Call (Domain  => EW_Term,
                                              Name    => Name,
                                              Binders => Binders);
      Equality : W_Pred_Id;
      Node_Name : constant String := (if Ada_Node /= Empty then
                                         Short_Name (Ada_Node)
                                      else "");
      Axiom_Name : constant String := (if Node_Name /= "" then
                                          Node_Name & "__"
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
     return W_Binder_Array is

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
      Binders  : Binder_Array)
     return W_Expr_Id is
   begin
      return New_Call
        (Ada_Node => Ada_Node,
         Domain   => Domain,
         Name     => Name,
         Args     => New_Expr_Array (Domain, Binders));
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
      Result : W_Expr_Array (Binders'Range);
   begin
      if Binders'Length = 0 and then Domain = EW_Prog then
         return (1 => New_Void);
      else
         for B in Binders'Range loop
            Result (B) := +Binders (B).B_Name;
         end loop;
      end if;

      return Result;
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
             (Binders => Binders,
              Triggers => Triggers,
              Pred    => Ax_Body));
   end New_Guarded_Axiom;

   ---------------------------
   -- New_Record_Definition --
   ---------------------------

   function New_Record_Definition
      (Ada_Node : Node_Id := Empty;
       Name     : W_Name_Id;
       Binders  : Binder_Array) return W_Declaration_Id is
   begin
      return
         New_Type_Decl
           (Ada_Node   => Ada_Node,
            Name       => Name,
            Labels     => Name_Id_Sets.Empty_Set,
            Definition =>
              New_Record_Definition
                (Fields => New_Binders (EW_Pred, Binders)));
   end New_Record_Definition;

   ---------------------------
   -- New_Universal_Quantif --
   ---------------------------

   function New_Universal_Quantif
     (Ada_Node : Node_Id := Empty;
      Binders  : Binder_Array;
      Triggers : W_Triggers_OId := Why_Empty;
      Pred     : W_Pred_Id) return W_Pred_Id
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
            if Eq_Base (Get_Type (+B.B_Name), Typ) then
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
               if Eq_Base (Get_Type (+B.B_Name), Typ) then
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
                    New_Universal_Quantif (Ada_Node  => Empty,
                                           Binders   => Other_Binders,
                                           Triggers  => Triggers,
                                           Pred      => Pred));
            end if;
         end;
      end if;
   end New_Universal_Quantif;

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
         when Regular =>
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

   function To_Binder_Array (A : Item_Array) return Binder_Array is
      Result : Binder_Array (1 .. Item_Array_Length (A));
      Count  : Natural := 1;
   begin
      for Index in A'Range loop
         declare
            Cur : Item_Type renames A (Index);
         begin
            case Cur.Kind is
               when Regular =>
                  Result (Count) := Cur.Main;
                  Count := Count + 1;
               when UCArray =>
                  Result (Count) := Cur.Content;
                  Count := Count + 1;
                  for Dim_Index in 1 .. Cur.Dim loop
                     Result (Count) :=
                       (B_Name => Cur.Bounds (Dim_Index).First,
                        others => <>);
                     Result (Count + 1) :=
                       (B_Name => Cur.Bounds (Dim_Index).Last,
                        others => <>);
                     Count := Count + 2;
                  end loop;
               when DRecord =>
                  if Cur.Fields.Present then
                     Result (Count) := Cur.Fields.Binder;
                     Count := Count + 1;
                  end if;
                  if Cur.Discrs.Present then
                     Result (Count) := Cur.Discrs.Binder;
                     Count := Count + 1;
                  end if;
                  if Cur.Constr.Present then
                     Result (Count) :=
                       (B_Name => Cur.Constr.Id,
                        others => <>);
                     Count := Count + 1;
                  end if;
                  if Cur.Tag.Present then
                     Result (Count) :=
                       (B_Name => Cur.Tag.Id,
                        others => <>);
                     Count := Count + 1;
                  end if;
               when Func    =>
                  raise Program_Error;
            end case;
         end;
      end loop;
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
         B_Ent    => null,
         Mutable  => False,
         Ada_Node => Empty);
   end Unit_Param;

end Why.Gen.Binders;
