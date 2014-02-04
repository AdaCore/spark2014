------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - T Y P E S                         --
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

--  For debugging, to print info on the output before raising an exception
with Ada.Text_IO;
use Ada.Text_IO;

with GNAT.Source_Info;

with Atree;              use Atree;
with Einfo;              use Einfo;
with Namet;              use Namet;
with Sinfo;              use Sinfo;
with Sinput;             use Sinput;
with Stand;              use Stand;

with SPARK_Definition;   use SPARK_Definition;
with SPARK_Util;         use SPARK_Util;

with Why;                use Why;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Atree.Modules;  use Why.Atree.Modules;
with Why.Conversions;    use Why.Conversions;
with Why.Gen.Arrays;     use Why.Gen.Arrays;
with Why.Gen.Binders;    use Why.Gen.Binders;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Expr;       use Why.Gen.Expr;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Records;    use Why.Gen.Records;
with Why.Gen.Scalars;    use Why.Gen.Scalars;
with Why.Gen.Terms;      use Why.Gen.Terms;
with Why.Inter;          use Why.Inter;
with Why.Sinfo;          use Why.Sinfo;
with Why.Types;          use Why.Types;

with Gnat2Why.Nodes;     use Gnat2Why.Nodes;

package body Gnat2Why.Types is

   procedure Declare_Private_Type
     (Theory : W_Theory_Declaration_Id;
      E      : Entity_Id);
   --  Make the necessary declarations for a private type

   --------------------------
   -- Declare_Private_Type --
   --------------------------

   procedure Declare_Private_Type
     (Theory : W_Theory_Declaration_Id;
      E      : Entity_Id) is
      Discr    : Entity_Id := First_Discriminant (E);
      X_Binder : constant Binder_Type :=
        Binder_Type'(B_Name =>
                       New_Identifier (Name => "x",
                                       Typ  => EW_Private_Type),
                     others => <>);
      Y_Binder : constant Binder_Type :=
        Binder_Type'(B_Name =>
                       New_Identifier (Name => "y",
                                       Typ  => EW_Private_Type),
                     others => <>);

   begin

      --  We define a name for this type, as well as accessors for the
      --  discriminants

      Emit (Theory,
            New_Type_Decl
              (New_Identifier (Name => Short_Name (E)),
               Alias => EW_Private_Type));
      while Present (Discr) loop
         Emit
           (Theory,
            Why.Gen.Binders.New_Function_Decl
              (Ada_Node    => E,
               Domain      => EW_Term,
               Name        => To_Why_Id (Discr, Local => True),
               Return_Type => EW_Abstract (Etype (Discr)),
               Labels      => Name_Id_Sets.Empty_Set,
               Binders     => (1 => X_Binder)));
         Next_Discriminant (Discr);
      end loop;
      Emit
        (Theory,
         Why.Gen.Binders.New_Function_Decl
           (Domain      => EW_Term,
            Name        => To_Ident (W => WNE_Bool_Eq),
            Return_Type => EW_Bool_Type,
            Binders     => (1 => X_Binder, 2 => Y_Binder),
            Labels      => Name_Id_Sets.Empty_Set));
      Emit
        (Theory,
         Why.Gen.Binders.New_Function_Decl
           (Domain      => EW_Term,
            Name        => New_Identifier (Name => "user_eq"),
            Return_Type => EW_Bool_Type,
            Binders     => (1 => X_Binder, 2 => Y_Binder),
            Labels      => Name_Id_Sets.Empty_Set));
   end Declare_Private_Type;

   ------------------------------
   -- Generate_Type_Completion --
   ------------------------------

   procedure Generate_Type_Completion
     (File       : in out Why_Section;
      E          : Entity_Id)
   is
      Name : constant String := Full_Name (E) & Axiom_Theory_Suffix;
      Eq   : Entity_Id := Has_User_Defined_Eq (E);
      Ty   : constant W_Type_Id := EW_Abstract (E);
   begin
      Open_Theory
        (File, Name,
         Comment =>
           "Module giving axioms for the type entity "
         & """" & Get_Name_String (Chars (E)) & """"
         & (if Sloc (E) > 0 then
              " defined at " & Build_Location_String (Sloc (E))
           else "")
         & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  This module only contains an axiom when there is a user-provided
      --  equality

      if Present (Eq)
        and then Entity_In_SPARK (Eq)
      then

         --  we may need to adjust for renamed subprograms

         if Present (Renamed_Entity (Eq)) then
            Eq := Renamed_Entity (Eq);
         end if;

         declare
            Need_Convert : constant Boolean :=
              Is_Scalar_Type (E) and then not Is_Boolean_Type (E);
            Var_A : constant W_Identifier_Id :=
              New_Identifier (Ada_Node => E,
                              Name     => "a",
                              Typ      => Ty);
            Var_B : constant W_Identifier_Id :=
              New_Identifier (Ada_Node => E,
                              Name     => "b",
                              Typ      => Ty);
            Arg_A : constant W_Expr_Id :=
              (if Need_Convert then
                  Insert_Simple_Conversion
                 (Domain => EW_Term,
                  Expr   => +Var_A,
                  To     => Base_Why_Type (Ty))
               else +Var_A);
            Arg_B : constant W_Expr_Id :=
              (if Need_Convert then
                  Insert_Simple_Conversion
                 (Domain => EW_Term,
                  Expr   => +Var_B,
                  To     => Base_Why_Type (Ty))
               else +Var_B);
            Def   : constant W_Expr_Id :=
              New_Call
                (Ada_Node => Eq,
                 Domain   => EW_Pred,
                 Name     => To_Why_Id (E => Eq,
                                        Domain => EW_Pred,
                                        Typ => EW_Bool_Type),
                 Args     => (1 => Arg_A, 2 => Arg_B),
                 Typ      => EW_Bool_Type);
         begin
            Emit
              (File.Cur_Theory,
               New_Defining_Axiom
                 (Ada_Node    => E,
                  Binders     =>
                    (1 => Binder_Type'(B_Name => Var_A, others => <>),
                     2 => Binder_Type'(B_Name => Var_B, others => <>)),
                  Name        =>
                    New_Identifier
                      (Module => E_Module (E),
                       Name    => "user_eq"),
                  Return_Type => EW_Bool,
                  Def         => +Def));
         end;
      end if;
      Close_Theory (File,
                    Kind => Axiom_Theory,
                    Defined_Entity => E);
   end Generate_Type_Completion;

   -----------------------
   -- Ident_Of_Ada_Type --
   -----------------------

   function Ident_Of_Ada_Type (E : Entity_Id) return W_Identifier_Id
   is
   begin
      if Is_Standard_Boolean_Type (E) then
         return New_Identifier (Name => "bool");
      elsif Fullview_Not_In_SPARK (E) and then
        not Type_Based_On_External_Axioms (E)
      then
         return New_Identifier (Name => To_String (WNE_Private));
      else
         return To_Why_Id (E);
      end if;
   end Ident_Of_Ada_Type;

   --------------------
   -- Translate_Type --
   --------------------

   procedure Translate_Type
     (File       : in out Why_Section;
      E          : Entity_Id;
      New_Theory : out Boolean)
   is
      procedure Translate_Underlying_Type
        (Theory : W_Theory_Declaration_Id;
         E      : Entity_Id);
      --  Translate a non-private type entity E

      -------------------------------
      -- Translate_Underlying_Type --
      -------------------------------

      procedure Translate_Underlying_Type
        (Theory : W_Theory_Declaration_Id;
         E      : Entity_Id) is

         procedure Declare_Private_Type (Theory : W_Theory_Declaration_Id;
                                         E      : Entity_Id;
                                         Base_E : Entity_Id);

         --  Translation for private types based on packages with external
         --  axioms. It contains a logic type t, two conversion functions
         --  of_base and to_base and a discriminant check if needed.

         procedure Declare_Private_Type (Theory : W_Theory_Declaration_Id;
                                         E      : Entity_Id;
                                         Base_E : Entity_Id) is

            Constrained : constant Boolean :=
              Has_Discriminants (E) and then Is_Constrained (E);
            Base_Id     : constant W_Identifier_Id :=
              To_Why_Id (Base_E);
            E_Id        : constant W_Identifier_Id :=
              To_Why_Id (E, Local => True);
            E_Type      : constant W_Type_Id :=
              New_Named_Type (Name => E_Id);
            A_Ident     : constant W_Identifier_Id :=
              New_Identifier (Name     => "a",
                              Typ      => E_Type);
            To_Base_A   : constant W_Expr_Id :=
              New_Call (Domain   => EW_Term,
                        Name     => To_Ident (WNE_To_Base),
                        Args     => (1 => +A_Ident),
                        Typ      => EW_Abstract (Base_E));
            B_Ident     : constant W_Identifier_Id :=
              New_Identifier (Name     => "b",
                              Typ      => E_Type);
            To_Base_B   : constant W_Expr_Id :=
              New_Call (Domain   => EW_Term,
                        Name     => To_Ident (WNE_To_Base),
                        Args     => (1 => +B_Ident),
                        Typ      => EW_Abstract (Base_E));
            Comparison  : constant W_Pred_Id :=
              +New_Ada_Equality
              (Typ    => Base_E,
               Domain => EW_Pred,
               Left   => To_Base_A,
               Right  => To_Base_B,
               Force_Predefined => False);
         begin
            Add_Use_For_Entity (File,
                                Base_E,
                                EW_Clone_Default,
                                With_Completion => False);

            --  New type declaration. If the type is unconstrained, we only
            --  create an alias.

            if Constrained then
               Emit (Theory,
                     New_Type_Decl (Name => Short_Name (E)));
            else
               Emit (Theory,
                     New_Type_Decl (Name  => E_Id,
                                    Alias => EW_Abstract (Base_E)));
            end if;

            --  Declare range functions.

            if Has_Discriminants (E) then
               Declare_Conversion_Check_Function (Theory, E, Base_E);
            end if;

            --  Clone the appropriate module in Ada_Model_File.

            if Constrained then
               Emit (Theory,
                     New_Clone_Declaration
                       (Theory_Kind   => EW_Module,
                        Clone_Kind    => EW_Export,
                        Origin        => New_Module
                          (File => Ada_Model_File,
                           Name => NID ("Constrained_Private_Type")),
                        Substitutions =>
                          (1 => New_Clone_Substitution
                               (Kind      => EW_Type_Subst,
                                Orig_Name => To_Ident (WNE_Type),
                                Image     => E_Id),
                           2 => New_Clone_Substitution
                             (Kind      => EW_Type_Subst,
                              Orig_Name => To_Ident (WNE_Base_Type),
                              Image     => Base_Id))));

               --  If the type is constrained, generate range_axiom and
               --  coerce_axiom. We must generate those as range_pred may
               --  have different signatures.

               declare
                  Range_Expr  : constant W_Expr_Id :=
                    New_Call (Domain   => EW_Pred,
                              Name     => To_Ident (WNE_Range_Pred),
                              Args     => Prepare_Args_For_Subtype_Check
                                (E, To_Base_A));
                  X_Ident     : constant W_Identifier_Id :=
                    New_Identifier (Name     => "x",
                                    Typ      => EW_Abstract (Base_E));
                  Coerce_Expr : constant W_Expr_Id :=
                    New_Call (Domain   => EW_Term,
                              Name     => To_Ident (WNE_To_Base),
                              Args     =>
                                (1 => New_Call
                                     (Domain   => EW_Term,
                                      Name     => To_Ident (WNE_Of_Base),
                                      Args     => (1 => +X_Ident),
                                      Typ      => E_Type)),
                              Typ      => EW_Abstract (Base_E));
                  Coerce_Pred : constant W_Expr_Id :=
                    New_Relation
                      (Domain   => EW_Pred,
                       Op_Type  => EW_Abstract,
                       Left     => Coerce_Expr,
                       Op       => EW_Eq,
                       Right    => +X_Ident);
               begin
                  Emit (Theory,
                        New_Axiom
                          (Name     =>
                             NID (Short_Name (E) & "__range_axiom"),
                           Def      =>
                             New_Universal_Quantif
                               (Binders  =>
                                    (1 => Binder_Type'(B_Name => A_Ident,
                                                       others => <>)),
                                Triggers =>
                                  New_Triggers
                                    (Triggers =>
                                       (1 => New_Trigger
                                          (Terms => (1 => To_Base_A)))),
                                Pred     => +Range_Expr)));
                  Emit (Theory,
                        New_Axiom
                          (Name     =>
                             NID (Short_Name (E) & "__coerce_axiom"),
                           Def      =>
                             New_Universal_Quantif
                               (Binders  =>
                                    (1 => Binder_Type'(B_Name => X_Ident,
                                                       others => <>)),
                                Triggers =>
                                  New_Triggers
                                    (Triggers =>
                                       (1 => New_Trigger
                                          (Terms => (1 => Coerce_Expr)))),
                                Pred     => +Coerce_Pred)));
               end;
            else
               Emit (Theory,
                     New_Clone_Declaration
                       (Theory_Kind   => EW_Module,
                        Clone_Kind    => EW_Export,
                        Origin        => New_Module
                          (File => Ada_Model_File,
                           Name => NID ("Unconstrained_Private_Type")),
                        Substitutions =>
                          (1 => New_Clone_Substitution
                               (Kind      => EW_Type_Subst,
                                Orig_Name => To_Ident (WNE_Type),
                                Image     => E_Id))));
            end if;

            --  Declare equality functions using equality on the base type.

            Emit
              (Theory,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => To_Ident (WNE_Bool_Eq),
                  Binders     =>
                    Binder_Array'(1 =>
                                      Binder_Type'(B_Name => A_Ident,
                                                   others => <>),
                                  2 =>
                                    Binder_Type'(B_Name => B_Ident,
                                                 others => <>)),
                  Return_Type => +EW_Bool_Type,
                  Labels      => Name_Id_Sets.Empty_Set,
                  Def         => New_Conditional
                    (Domain    => EW_Term,
                     Condition => +Comparison,
                     Then_Part => +True_Term,
                     Else_Part => +False_Term)));
            Emit
              (Theory,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => New_Identifier (Name => "user_eq"),
                  Return_Type => EW_Bool_Type,
                  Binders     =>
                    Binder_Array'(1 =>
                                      Binder_Type'(B_Name => A_Ident,
                                                   others => <>),
                                  2 =>
                                    Binder_Type'(B_Name => B_Ident,
                                                 others => <>)),
                  Labels      => Name_Id_Sets.Empty_Set));
         end Declare_Private_Type;

      begin
         if Type_Based_On_External_Axioms (E) and then
           Ekind (Underlying_External_Axioms_Type (E)) in Private_Kind
         then
            Declare_Private_Type (Theory, E,
                                  Underlying_External_Axioms_Type (E));
         else
            case Ekind (E) is
            when Scalar_Kind =>
               Declare_Scalar_Type (Theory, E);

            when Array_Kind =>
               Declare_Ada_Array (Theory, E);

            when E_Record_Type | E_Record_Subtype =>
               Declare_Ada_Record (File, Theory, E);

            when Private_Kind =>
               Declare_Private_Type (Theory, E);

            when others =>
               Ada.Text_IO.Put_Line ("[Translate_Underlying_Type] ekind ="
                                     & Entity_Kind'Image (Ekind (E)));
               raise Not_Implemented;
            end case;
         end if;
      end Translate_Underlying_Type;

      Name : constant String := Full_Name (E);

      --  Start of Translate_Type

   begin
      if Is_Standard_Boolean_Type (E) or else E = Universal_Fixed then
         New_Theory := False;
         return;

      else
         New_Theory := True;

         Open_Theory
           (File, Name,
            Comment =>
              "Module for axiomatizing type "
            & """" & Get_Name_String (Chars (E)) & """"
            & (if Sloc (E) > 0 then
                 " defined at " & Build_Location_String (Sloc (E))
              else "")
            & ", created in " & GNAT.Source_Info.Enclosing_Entity);

         Translate_Underlying_Type (File.Cur_Theory, E);

         --  We declare a default value for all types, in principle.
         --  Cloned subtypes are a special case, they do not need such a
         --  definition.

         if Is_Record_Type (E) and then
           (if Ekind (E) = E_Record_Subtype then
                not (Present (Cloned_Subtype (E))))
         then
            Emit
              (File.Cur_Theory,
               Why.Atree.Builders.New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => To_Ident (WNE_Dummy),
                  Binders     => (1 .. 0 => <>),
                  Labels      => Name_Id_Sets.Empty_Set,
                  Return_Type =>
                    +New_Named_Type (Name => To_Why_Id (E, Local => True))));
         end if;

         --  If E is the full view of a private type, use its partial view as
         --  the filtering entity, as it is the entity used everywhere in AST.

         if Is_Full_View (E) then
            Close_Theory (File,
                          Kind => Definition_Theory,
                          Defined_Entity => Partial_View (E));
         else
            Close_Theory (File,
                          Kind => Definition_Theory,
                          Defined_Entity => E);
         end if;
      end if;
   end Translate_Type;

end Gnat2Why.Types;
