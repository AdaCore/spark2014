------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - R E C O R D S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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

with Ada.Containers.Hashed_Maps;

with Atree;              use Atree;
with Einfo;              use Einfo;
with Nlists;             use Nlists;

with Gnat2Why.Driver;    use Gnat2Why.Driver;
with Gnat2Why.Expr;      use Gnat2Why.Expr;
with Gnat2Why.Nodes;     use Gnat2Why.Nodes;
with Gnat2Why.Types;     use Gnat2Why.Types;
with Sinfo;              use Sinfo;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Conversions;    use Why.Conversions;
with Why.Gen.Binders;    use Why.Gen.Binders;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Expr;       use Why.Gen.Expr;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Preds;      use Why.Gen.Preds;
with Why.Sinfo;          use Why.Sinfo;
with Why.Types;          use Why.Types;

--  with Why.Gen.Terms;             use Why.Gen.Terms;

package body Why.Gen.Records is

   type Component_Info is record
      Parent_Variant  : Node_Id;
      Parent_Var_Part : Node_Id;
      Ident           : W_Identifier_Id;
   end record;

   package Info_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Component_Info,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   -----------------------
   -- Define_Ada_Record --
   -----------------------

   procedure Declare_Ada_Record
     (File    : in out Why_File;
      Theory  : W_Theory_Declaration_Id;
      E       : Entity_Id)
   is

      function Count_Why_Record_Fields (E : Entity_Id) return Natural;
      --  count the number of fields

      procedure Declare_Record_Type;
      --  declare the record type

      procedure Declare_Protected_Access_Functions;
      --  for each record field, declare an access program function, whose
      --  result is the same as the record field access, but there is a
      --  precondition (when needed)

      function Compute_Discriminant_Check (Info  : Component_Info)
                                           return W_Pred_Id;
      --  compute the discriminant check for an access to the given field, as a
      --  predicate which can be used as a precondition

      function Compute_Others_Choice (Info  : Component_Info;
                                      Discr : W_Term_Id) return W_Pred_Id;
      --  compute (part of) the discriminant check for one discriminant in the
      --  special case where the N_Discrete_Choice is actually an
      --  N_Others_Choice

      function Is_Others_Choice (N : Node_Id) return Boolean;
      --  Check whether the N_Variant is actually an N_Others_Choice

      function Transform_Discrete_Choices (Case_N : Node_Id;
                                           Expr   : W_Term_Id)
                                           return W_Pred_Id;
      --  Wrapper for the function in Gnat2Why.Expr;

      procedure Init_Component_Info;
      --  Initialize the map which maps each component to its information
      --  record

      Ty_Ident   : constant W_Identifier_Id := To_Ident (WNE_Type);
      Comp_Info  : Info_Maps.Map := Info_Maps.Empty_Map;
      --  This map maps each component and each N_Variant node to a
      --  Component_Info record. This map is initialized by a call to
      --  Init_Component_Info;

      Decl_Node  : constant Node_Id := Parent (E);
      Components : constant Node_Id :=
        Component_List (Type_Definition (Decl_Node));

      A_Ident    : constant W_Identifier_Id := New_Identifier (Name => "a");
      R_Binder   : constant Binder_Array :=
        (1 => (B_Name => A_Ident,
               B_Type =>
                 New_Abstract_Type (Name => Ty_Ident),
               others => <>));

      --------------------------------
      -- Compute_Discriminant_Check --
      --------------------------------

      function Compute_Discriminant_Check (Info  : Component_Info)
                                           return W_Pred_Id
      is
         Local_Info : Component_Info := Info;
         Cond       : W_Pred_Id := True_Pred;
      begin
         while Present (Local_Info.Parent_Variant) loop
            declare
               Ada_Discr : constant Node_Id :=
                 Entity (Name (Local_Info.Parent_Var_Part));
               Discr : constant W_Term_Id :=
                 +Insert_Conversion
                   (Domain => EW_Term,
                    Expr =>
                      New_Record_Access
                        (Name  => +A_Ident,
                         Field => Comp_Info.Element (Ada_Discr).Ident),
                    To   => EW_Int_Type,
                    From => EW_Abstract (Etype (Ada_Discr)));
               New_Cond : constant W_Pred_Id :=
                 (if Is_Others_Choice (Local_Info.Parent_Variant) then
                  Compute_Others_Choice (Local_Info, Discr)
                  else
                  +Transform_Discrete_Choices
                    (Local_Info.Parent_Variant, Discr));
            begin
               Cond :=
                 +New_And_Then_Expr
                 (Domain => EW_Pred,
                  Left   => +Cond,
                  Right  => +New_Cond);
               Local_Info := Comp_Info.Element (Local_Info.Parent_Var_Part);
            end;
         end loop;
         return Cond;
      end Compute_Discriminant_Check;

      ---------------------------
      -- Compute_Others_Choice --
      ---------------------------

      function Compute_Others_Choice (Info  : Component_Info;
                                      Discr : W_Term_Id) return W_Pred_Id
      is
         Var_Part : constant Node_Id := Info.Parent_Var_Part;
         Var      : Node_Id := First (Variants (Var_Part));
         Cond     : W_Pred_Id := True_Pred;
      begin
         while Present (Var) loop
            if not Is_Others_Choice (Var) then
               Cond :=
                 +New_And_Then_Expr
                   (Domain => EW_Pred,
                    Left   => +Cond,
                    Right  =>
                      New_Not
                        (Domain => EW_Pred,
                         Right  =>
                           +Transform_Discrete_Choices (Var, Discr)));
            end if;
            Next (Var);
         end loop;
         return Cond;
      end Compute_Others_Choice;

      -----------------------------
      -- Count_Why_Record_Fields --
      -----------------------------

      function Count_Why_Record_Fields (E : Entity_Id) return Natural
      is
         Cnt : Natural := 0;
         Field : Node_Id := First_Component_Or_Discriminant (E);
      begin
         while Present (Field) loop
            Next_Component_Or_Discriminant (Field);
            Cnt := Cnt + 1;
         end loop;
         return Cnt;
      end Count_Why_Record_Fields;

      ----------------------------------------
      -- Declare_Protected_Access_Functions --
      ----------------------------------------

      procedure Declare_Protected_Access_Functions
      is
         Field : Entity_Id := First_Component_Or_Discriminant (E);
      begin
         while Present (Field) loop
            declare
               Info : constant Component_Info :=
                 Comp_Info.Element (Key => Field);
               Prog_Name : constant W_Identifier_Id :=
                 To_Program_Space (Info.Ident);
            begin
               Emit (Theory,
                     New_Function_Decl
                       (Domain      => EW_Prog,
                        Name        => Prog_Name,
                        Binders     => R_Binder,
                        Return_Type =>
                          Why_Logic_Type_Of_Ada_Type (Etype (Field)),
                        Pre         =>
                          Compute_Discriminant_Check (Info),
                        Post        =>
                          New_Relation
                            (Left    => +To_Ident (WNE_Result),
                             Op_Type => EW_Abstract,
                             Op      => EW_Eq,
                             Right   =>
                               New_Record_Access
                                 (Name => +A_Ident,
                                  Field => Info.Ident))));
               Next_Component_Or_Discriminant (Field);
            end;
         end loop;
      end Declare_Protected_Access_Functions;

      -------------------------
      -- Declare_Record_Type --
      -------------------------

      procedure Declare_Record_Type
      is
         Num_Fields : constant Natural := Count_Why_Record_Fields (E);
         Binders    : Binder_Array (1 .. Num_Fields);
         Field      : Entity_Id := First_Component_Or_Discriminant (E);
      begin
         if Num_Fields = 0 then
            Emit
              (Theory,
               New_Type (To_String (WNE_Type)));
            return;
         end if;
         for Index in 1 .. Num_Fields loop
            Binders (Index) :=
              (B_Name => To_Why_Id (Field, Local => True),
               B_Type =>
                 Why_Logic_Type_Of_Ada_Type (Etype (Field)),
               others => <>);
            Next_Component_Or_Discriminant (Field);
         end loop;
         Emit (Theory,
           New_Record_Definition (Name    => Ty_Ident,
                                  Binders => Binders));
      end Declare_Record_Type;

      -------------------------
      -- Init_Component_Info --
      -------------------------

      procedure Init_Component_Info is
         procedure Mark_Component_List (N : Node_Id;
                                        Parent_Var_Part : Node_Id;
                                        Parent_Variant  : Node_Id);

         procedure Mark_Variant_Part (N : Node_Id;
                                      Parent_Var_Part : Node_Id;
                                      Parent_Variant  : Node_Id);

         --------------------------
         -- Mark_Component_Items --
         --------------------------

         procedure Mark_Component_List (N : Node_Id;
                                         Parent_Var_Part : Node_Id;
                                         Parent_Variant  : Node_Id) is
            Field : Node_Id := First (Component_Items (N));
         begin
            while Present (Field) loop
               Comp_Info.Insert
                 (Defining_Identifier (Field),
                  Component_Info'(
                    Parent_Variant  => Parent_Variant,
                    Parent_Var_Part => Parent_Var_Part,
                    Ident           =>
                      To_Why_Id (Defining_Identifier (Field),
                                 Local => True)));
               Next (Field);
            end loop;
            if Present (Variant_Part (N)) then
               Mark_Variant_Part (Variant_Part (N),
                                  Parent_Var_Part,
                                  Parent_Variant);
            end if;
         end Mark_Component_List;

         -----------------------
         -- Mark_Variant_Part --
         -----------------------

         procedure Mark_Variant_Part (N : Node_Id;
                                      Parent_Var_Part : Node_Id;
                                      Parent_Variant  : Node_Id) is
            Var : Node_Id := First (Variants (N));
         begin
            Comp_Info.Insert (N, Component_Info'(
              Parent_Variant  => Parent_Variant,
              Parent_Var_Part => Parent_Var_Part,
              Ident           => Why_Empty));
            while Present (Var) loop
               Mark_Component_List (Component_List (Var), N, Var);
               Next (Var);
            end loop;
         end Mark_Variant_Part;

         Field : Node_Id := First (Discriminant_Specifications (Decl_Node));
      begin
         while Present (Field) loop
            Comp_Info.Insert
              (Defining_Identifier (Field),
               Component_Info'
                 (Parent_Variant  => Empty,
                  Parent_Var_Part => Empty,
                  Ident           =>
                    To_Why_Id (Defining_Identifier (Field),
                      Local => True)));
            Next (Field);
         end loop;
         Mark_Component_List (Components, Empty, Empty);
      end Init_Component_Info;

      ----------------------
      -- Is_Others_Choice --
      ----------------------

      function Is_Others_Choice (N : Node_Id) return Boolean
      is
         Choices : constant List_Id := Discrete_Choices (N);
      begin
         return List_Length (Choices) = 1 and then
                 Nkind (First (Choices)) = N_Others_Choice;
      end Is_Others_Choice;

      --------------------------------
      -- Transform_Discrete_Choices --
      --------------------------------

      function Transform_Discrete_Choices (Case_N : Node_Id;
                                           Expr   : W_Term_Id)
                                           return W_Pred_Id
      is
         Params : constant Translation_Params :=
           (Theory      => File.Cur_Theory,
            File        => File.File,
            Phase       => Translation,
            Gen_Image   => False,
            Ref_Allowed => True,
            Name_Map    => Ada_Ent_To_Why.Empty_Map);
      begin
         return +Gnat2Why.Expr.Transform_Discrete_Choices
           (Case_N       => Case_N,
            Matched_Expr => +Expr,
            Cond_Domain  => EW_Pred,
            Params       => Params);
      end Transform_Discrete_Choices;

   begin
      Init_Component_Info;
      Declare_Record_Type;
      Declare_Protected_Access_Functions;
   end Declare_Ada_Record;

end Why.Gen.Records;
