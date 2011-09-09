------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - B I N D E R S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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

with Why.Conversions; use Why.Conversions;
with Why.Gen.Names;   use Why.Gen.Names;
with Why.Gen.Decl;    use Why.Gen.Decl;
with Why.Gen.Terms;   use Why.Gen.Terms;
with Why.Gen.Preds;   use Why.Gen.Preds;
with Why.Gen.Progs;   use Why.Gen.Progs;
with Why.Inter;       use Why.Inter;

package body Why.Gen.Binders is

   function New_Computation_Type
     (Ada_Node    : Node_Id := Empty;
      Domain      : EW_Domain;
      Binders     : Binder_Array;
      Return_Type : W_Primitive_Type_Id;
      Effects     : W_Effects_Id := New_Effects;
      Pre         : W_Pred_Id :=
                      New_Literal (Value => EW_True, Domain => EW_Pred);
      Post        : W_Pred_Id :=
                      New_Literal (Value => EW_True, Domain => EW_Pred))
     return W_Computation_Type_Id;

   function New_Binders
     (Domain  : EW_Domain;
      Binders : Binder_Array)
     return W_Binder_Array;

   function New_Expr_Array
     (Domain  : EW_Domain;
      Binders : Binder_Array)
     return W_Expr_Array;

   ---------------------------------
   -- Emit_Top_Level_Declarations --
   ---------------------------------

   procedure Emit_Top_Level_Declarations
     (File        : W_File_Id;
      Ada_Node    : Node_Id := Empty;
      Name        : W_Identifier_Id;
      Binders     : Binder_Array;
      Return_Type : W_Primitive_Type_Id;
      Spec        : Declaration_Spec_Array)
   is
      Spec0 : Declaration_Spec_Array := Spec;
   begin
      Set_Top_Level_Declarations
        (File, Ada_Node, Name, Binders, Return_Type, Spec0);
   end Emit_Top_Level_Declarations;

   -----------------
   -- New_Binders --
   -----------------

   function New_Binders
     (Anonymous_Binders : W_Primitive_Type_Array)
     return Binder_Array
   is
      Result : Binder_Array (Anonymous_Binders'Range);
      N      : Character := 'a';
   begin
      for J in Anonymous_Binders'Range loop
         Result (J) :=
           (B_Name =>
              New_Identifier ("dummy__" & N),
            B_Type =>
              Anonymous_Binders (J),
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
      Left     : constant W_Term_Id :=
                   +New_Call
                     (Domain  => EW_Term,
                      Name    => Name,
                      Binders => Binders);
      Equality : constant W_Pred_Id :=
                   New_Relation
                     (Op      => EW_Eq,
                      Op_Type => Return_Type,
                      Left    => +Left,
                      Right   => +Def);
   begin
      return New_Guarded_Axiom
        (Ada_Node => Ada_Node,
         Name     => Logic_Func_Axiom.Id (Name),
         Binders  => Binders,
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
   begin
      return New_Guarded_Axiom
        (Ada_Node => Ada_Node,
         Name     => Logic_Func_Axiom.Id (Name),
         Binders  => Binders,
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
        return W_Simple_Value_Type_Id;

      ------------------
      -- New_Arg_Type --
      ------------------

      function New_Arg_Type
        (Binder : Binder_Type)
        return W_Simple_Value_Type_Id is
      begin
         if Domain = EW_Prog then
            case Binder.Modifier is
               when Array_Modifier =>
                  return New_Array_Type (Component_Type => Binder.B_Type);
               when Ref_Modifier =>
                  return New_Ref_Type (Aliased_Type => Binder.B_Type);
               when None =>
                  return +Binder.B_Type;
            end case;

         else
            return +Binder.B_Type;
         end if;
      end New_Arg_Type;

      Result : W_Binder_Array (Binders'Range);

   --  Start of processing for New_Binders

   begin
      for B in Binders'Range loop
         Result (B) := New_Binder
                         (Ada_Node => Binders (B).Ada_Node,
                          Name     => Binders (B).B_Name,
                          Arg_Type => New_Arg_Type (Binders (B)));
      end loop;

      return Result;
   end New_Binders;

   -----------------------
   -- New_Call_To_Logic --
   -----------------------

   function New_Call
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array)
     return W_Term_Id is
   begin
      return New_Call
        (Ada_Node => Ada_Node,
         Domain   => Domain,
         Name     => Name,
         Args     => New_Expr_Array (Domain, Binders));
   end New_Call;

   --------------------------
   -- New_Computation_Type --
   --------------------------

   function New_Computation_Type
     (Ada_Node    : Node_Id := Empty;
      Domain      : EW_Domain;
      Binders     : Binder_Array;
      Return_Type : W_Primitive_Type_Id;
      Effects     : W_Effects_Id := New_Effects;
      Pre         : W_Pred_Id :=
                      New_Literal (Value => EW_True, Domain => EW_Pred);
      Post        : W_Pred_Id :=
                      New_Literal (Value => EW_True, Domain => EW_Pred))
     return W_Computation_Type_Id is
   begin
      return New_Computation_Type
        (Ada_Node => Ada_Node,
         Domain   => Domain,
         Binders  => New_Binders (Domain, Binders),
         Pre      => Pre,
         Effects  => Effects,
         Post     => Post,
         Result   => New_Result (+Return_Type));
   end New_Computation_Type;

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
            Var_Type  => Binders (Binders'First).B_Type,
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
      Return_Type : W_Primitive_Type_Id;
      Effects     : W_Effects_Id := New_Effects;
      Pre         : W_Pred_Id :=
                      New_Literal (Value => EW_True, Domain => EW_Pred);
      Post        : W_Pred_Id :=
                      New_Literal (Value => EW_True, Domain => EW_Pred))
     return W_Declaration_Id is
   begin
      return New_Function_Decl
        (Ada_Node  => Ada_Node,
         Domain    => Domain,
         Name      => Name,
         Func_Type =>
           New_Computation_Type
             (Binders     => Binders,
              Domain      => Domain,
              Return_Type => Return_Type,
              Effects     => Effects,
              Pre         => Pre,
              Post        => Post));
   end New_Function_Decl;

   -----------------------
   -- New_Function_Def --
   -----------------------

   function New_Function_Def
     (Ada_Node    : Node_Id := Empty;
      Domain      : EW_Domain;
      Name        : W_Identifier_Id;
      Binders     : Binder_Array;
      Return_Type : W_Primitive_Type_OId := Why_Empty;
      Def         : W_Expr_Id;
      Pre         : W_Pred_Id :=
                      New_Literal (Value => EW_True, Domain => EW_Pred);
      Post        : W_Pred_Id :=
                      New_Literal (Value => EW_True, Domain => EW_Pred))
     return W_Declaration_Id
   is
      RT : constant W_Primitive_Type_Id :=
             (if Return_Type = Why_Empty then
                (case Domain is
                   when EW_Pred => New_Base_Type (Base_Type => EW_Bool),
                   when others  => New_Base_Type (Base_Type => EW_Unit))
             else Return_Type);
   begin
      return New_Function_Def
        (Ada_Node  => Ada_Node,
         Domain    => Domain,
         Spec      =>
           +New_Function_Decl
             (Domain      => Domain,
              Name        => Name,
              Binders     => Binders,
              Return_Type => RT,
              Pre         => Pre,
              Post        => Post),
         Def       => Def);
   end New_Function_Def;

   -----------------------
   -- New_Guarded_Axiom --
   -----------------------

   function New_Guarded_Axiom
     (Ada_Node : Node_Id := Empty;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array;
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
              Pred    => Ax_Body));
   end New_Guarded_Axiom;

   ---------------------------
   -- New_Universal_Quantif --
   ---------------------------

   function New_Universal_Quantif
     (Ada_Node : Node_Id := Empty;
      Binders  : Binder_Array;
      Pred     : W_Pred_Id)
     return W_Pred_Id is
   begin
      if Binders'Length = 0 then
         return Pred;
      else
         return New_Universal_Quantif
           (Ada_Node  => Ada_Node,
            Variables => (1 => Binders (Binders'First).B_Name),
            Var_Type  => Binders (Binders'First).B_Type,
            Pred      =>
              New_Universal_Quantif (Empty,
                                     Binders (Binders'First + 1
                                              .. Binders'Last),
                                     Pred));
      end if;
   end New_Universal_Quantif;

   --------------------------------
   -- Set_Top_Level_Declarations --
   --------------------------------

   procedure Set_Top_Level_Declarations
     (File        : W_File_Id;
      Ada_Node    : Node_Id := Empty;
      Name        : W_Identifier_Id;
      Binders     : Binder_Array;
      Return_Type : W_Primitive_Type_Id;
      Spec        : in out Declaration_Spec_Array)
   is
      Logic_Def_Emitted : Boolean := False;
   begin
      for S in Spec'Range loop
         case Spec (S).Kind is
            when W_Function_Decl =>
               case Spec (S).Domain is
                  when EW_Term =>
                     pragma Assert (not Logic_Def_Emitted);

                     if Spec (S).Name = Why_Empty then
                        Spec (S).Name := Logic_Func_Name.Id (Name);
                     end if;

                     Emit
                       (File,
                        New_Function_Decl
                          (Ada_Node    => Ada_Node,
                           Domain      => Spec (S).Domain,
                           Name        => Spec (S).Name,
                           Binders     => Binders,
                           Return_Type => Return_Type));
                     Logic_Def_Emitted := True;

                     if Spec (S).Def /= Why_Empty then
                        Emit
                          (File,
                           New_Defining_Axiom
                             (Ada_Node    => Ada_Node,
                              Name        => Spec (S).Name,
                              Return_Type => Get_EW_Type (Return_Type),
                              Binders     => Binders,
                              Pre         => Spec (S).Pre,
                              Def         => Spec (S).Def));
                     end if;

                  when EW_Pred =>
                     --  Invalid
                     pragma Assert (False);
                     null;

                  when EW_Prog =>
                     if Spec (S).Name = Why_Empty then
                        Spec (S).Name := Program_Func_Name.Id (Name);
                     end if;

                     if Spec (S).Pre = Why_Empty then
                        Spec (S).Pre := New_Literal (Value => EW_True);
                     end if;

                     if Spec (S).Post = Why_Empty then
                        if Logic_Def_Emitted then
                           Spec (S).Post :=
                             New_Relation
                               (Op_Type =>
                                  Get_EW_Type (Return_Type),
                                Left    =>
                                  +New_Call
                                    (Domain  => EW_Term,
                                     Name    => Spec (S).Name,
                                     Binders => Binders),
                                Op      => EW_Eq,
                                Right   => +New_Result_Term);
                        else
                           Spec (S).Post := New_Literal (Value => EW_True);
                        end if;
                     end if;

                     Emit
                       (File,
                        New_Function_Decl
                        (Ada_Node    => Ada_Node,
                         Domain      => EW_Prog,
                         Name        => Spec (S).Name,
                         Binders     => Binders,
                         Return_Type => Return_Type,
                         Pre         => Spec (S).Pre,
                         Effects     => Spec (S).Effects,
                         Post        => Spec (S).Post));
               end case;

            when W_Function_Def =>
               case Spec (S).Domain is
                  when EW_Term =>
                     pragma Assert (not Logic_Def_Emitted);
                     pragma Assert (Spec (S).Term /= Why_Empty);

                     if Spec (S).Name = Why_Empty then
                        Spec (S).Name := Logic_Func_Name.Id (Name);
                     end if;

                     Emit
                       (File,
                        New_Function_Def
                          (Ada_Node    => Ada_Node,
                           Domain      => Spec (S).Domain,
                           Name        => Spec (S).Name,
                           Binders     => Binders,
                           Return_Type => Return_Type,
                           Def         => +Spec (S).Term));
                     Logic_Def_Emitted := True;

                  when EW_Pred =>
                     if Spec (S).Name = Why_Empty then
                        Spec (S).Name := Logic_Func_Name.Id (Name);
                     end if;

                     Emit
                       (File,
                        New_Function_Def
                          (Ada_Node    => Ada_Node,
                           Domain      => Spec (S).Domain,
                           Name        => Spec (S).Name,
                           Binders     => Binders,
                           Def         => +Spec (S).Pred));

                  when EW_Prog =>
                     if Spec (S).Name = Why_Empty then
                        Spec (S).Name := New_Definition_Name.Id (Name);
                     end if;

                     if Spec (S).Pre = Why_Empty then
                        Spec (S).Pre := New_Literal (Value => EW_True);
                     end if;

                     if Spec (S).Post = Why_Empty then
                        Spec (S).Post := New_Literal (Value => EW_True);
                     end if;

                     Emit
                       (File,
                        New_Function_Def
                          (Ada_Node    => Ada_Node,
                           Domain      => Spec (S).Domain,
                           Name        => Spec (S).Name,
                           Binders     => Binders,
                           Pre         => Spec (S).Pre,
                           Def         => +Spec (S).Prog,
                           Post        => Spec (S).Post));
               end case;
         end case;
      end loop;
   end Set_Top_Level_Declarations;

end Why.Gen.Binders;
