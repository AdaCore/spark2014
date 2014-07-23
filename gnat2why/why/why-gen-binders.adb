------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - B I N D E R S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2014, AdaCore                   --
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

with Why.Atree.Modules; use Why.Atree.Modules;
with Why.Conversions;   use Why.Conversions;
with Why.Gen.Expr;      use Why.Gen.Expr;
with Why.Gen.Names;     use Why.Gen.Names;
with Why.Inter;         use Why.Inter;

with Gnat2Why.Nodes;

package body Why.Gen.Binders is

   function New_Binders
     (Domain  : EW_Domain;
      Binders : Binder_Array)
     return W_Binder_Array;

   function New_Expr_Array
     (Domain  : EW_Domain;
      Binders : Binder_Array)
     return W_Expr_Array;

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
      Return_Type : EW_Type;
      Pre         : W_Pred_OId := Why_Empty;
      Def         : W_Term_Id)
     return W_Declaration_Id
   is
      Left : constant W_Term_Id := +New_Call (Domain  => EW_Term,
                                              Name    => Name,
                                              Binders => Binders);
      Equality : W_Pred_Id;
      Node_Name : constant String := (if Ada_Node /= Empty then
                                         Gnat2Why.Nodes.Short_Name (Ada_Node)
                                      else "");
      Axiom_Name : constant String := (if Node_Name /= "" then
                                          Node_Name & "__"
                                       else "") & Def_Axiom;
   begin
      Equality :=
        New_Relation
          (Op      => EW_Eq,
           Op_Type => Return_Type,
           Left    => +Left,
           Right   => +Def);
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
        (if Ada_Node /= Empty then
            Gnat2Why.Nodes.Short_Name (Ada_Node) & "__"
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
            if Eq_Base_Type (Get_Type (+B.B_Name), Typ) then
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
               if Eq_Base_Type (Get_Type (+B.B_Name), Typ) then
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
