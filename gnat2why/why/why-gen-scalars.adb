------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - S C A L A R S                       --
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

with Sem_Eval;           use Sem_Eval;
with Sinfo;              use Sinfo;
with Snames;             use Snames;

with SPARK_Util;         use SPARK_Util;

with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Atree.Modules;  use Why.Atree.Modules;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Inter;          use Why.Inter;
with Why.Sinfo;          use Why.Sinfo;
with Why.Types;          use Why.Types;

with Gnat2Why.Nodes;     use Gnat2Why.Nodes;
with Gnat2Why.Util;      use Gnat2Why.Util;

package body Why.Gen.Scalars is

   procedure Define_Scalar_Attributes
     (Theory     : W_Theory_Declaration_Id;
      Base_Type  : EW_Scalar;
      First      : W_Term_Id;
      Last       : W_Term_Id;
      Modulus    : W_Term_OId);
   --  Define the attributes first, last, modulus for the given type.

   -------------------------
   -- Declare_Scalar_Type --
   -------------------------

   procedure Declare_Scalar_Type
     (Theory : W_Theory_Declaration_Id;
      E      : Entity_Id)
   is
      Why_Name  : constant W_Identifier_Id := To_Why_Id (E, Local => True);
      Is_Static : constant Boolean := not Type_Is_Modeled_As_Int_Or_Real (E);

      function Pick_Clone return W_Module_Id;
      --  Choose the correct module to clone

      function Compute_Clone_Subst return W_Clone_Substitution_Array;
      --  generate the substitutions to be passed to the clone

      -------------------------
      -- Compute_Clone_Subst --
      -------------------------

      function Compute_Clone_Subst return W_Clone_Substitution_Array is
         Has_Round_Real : constant Boolean :=
           Is_Single_Precision_Floating_Point_Type (E)
           or else
             Is_Double_Precision_Floating_Point_Type (E);
         Round_Id : constant W_Identifier_Id :=
           (if Is_Single_Precision_Floating_Point_Type (E) then
                 Floating_Round_Single
            elsif Is_Double_Precision_Floating_Point_Type (E) then
                 Floating_Round_Double
            else
               Floating_Round);
         Default_Clone_Subst : constant W_Clone_Substitution_Array :=
           (1 => New_Clone_Substitution
              (Kind      => EW_Type_Subst,
               Orig_Name => New_Identifier (Name => "t"),
               Image     => Why_Name));
         Round_Clone_Subst : constant W_Clone_Substitution_Array :=
           (if Has_Round_Real then
              (1 => New_Clone_Substitution
                   (Kind      => EW_Function,
                    Orig_Name => To_Ident (WNE_Float_Round_Tmp),
                    Image     => Round_Id))
            else (1 .. 0 => <>));
         Static_Clone_Subst : constant W_Clone_Substitution_Array :=
           (if Is_Static then
              (1 => New_Clone_Substitution
                   (Kind      => EW_Function,
                    Orig_Name => To_Ident (WNE_Attr_First),
                    Image     => To_Ident (WNE_Attr_First)),
               2 => New_Clone_Substitution
                 (Kind      => EW_Function,
                  Orig_Name => To_Ident (WNE_Attr_Last),
                  Image     => To_Ident (WNE_Attr_Last)))
            else (1 .. 0 => <>));
         Mod_Clone_Subst : constant W_Clone_Substitution_Array :=
           (if Is_Modular_Integer_Type (E) then
                (1 => New_Clone_Substitution
                 (Kind      => EW_Function,
                  Orig_Name => To_Ident (WNE_Attr_Modulus),
                  Image     => To_Ident (WNE_Attr_Modulus)))
            else (1 .. 0 => <>));
      begin

         --  If the type Entity has a rounding operation, use it in the clone
         --  substitution to replace the default one.

         return
           Default_Clone_Subst &
           Round_Clone_Subst &
           Static_Clone_Subst &
           Mod_Clone_Subst;
      end Compute_Clone_Subst;

      ----------------
      -- Pick_Clone --
      ----------------

      function Pick_Clone return W_Module_Id is
      begin
         if Is_Discrete_Type (E) then
            if Is_Static then
               if Is_Modular_Integer_Type (E) then
                  return Static_Modular;
               else
                  return Static_Discrete;
               end if;
            elsif Is_Modular_Integer_Type (E) then
               return Dynamic_Modular;
            else
               return Dynamic_Discrete;
            end if;
         elsif Is_Static then
            return Static_Floating_Point;
         else
            return Dynamic_Floating_Point;
         end if;
      end Pick_Clone;

      --  Local variables

      First, Last, Modul : W_Term_OId := Why_Empty;
      Rng                : constant Node_Id := Get_Range (E);
      --  beginning of processing for Declare_Scalar_Type

   begin

      --  declare the abstract type

      Emit (Theory,
            New_Type_Decl
              (Name => Why_Name,
               Labels => Name_Id_Sets.To_Set (NID ("""bounded_type"""))));

      --  retrieve and declare the attributes first, last and modulus

      if Is_Modular_Integer_Type (E) then
         Modul := New_Integer_Constant (Value => Modulus (E));
      end if;
      if Is_Static_Expression (Low_Bound (Rng)) then
         if Is_Discrete_Type (E) then
            First := New_Integer_Constant (Value =>
                                             Expr_Value (Low_Bound (Rng)));
         else
            First := New_Real_Constant (Value =>
                                          Expr_Value_R (Low_Bound (Rng)));
         end if;
      end if;
      if Is_Static_Expression (High_Bound (Rng)) then
         if Is_Discrete_Type (E) then
            Last := New_Integer_Constant (Value =>
                                            Expr_Value (High_Bound (Rng)));
         else
            Last := New_Real_Constant (Value =>
                                         Expr_Value_R (High_Bound (Rng)));
         end if;
      end if;
      Define_Scalar_Attributes (Theory    => Theory,
                                Base_Type =>
                                  (if Is_Discrete_Type (E) then EW_Int
                                   else EW_Real),
                                First     => First,
                                Last      => Last,
                                Modulus   => Modul);
      Emit (Theory,
            New_Clone_Declaration (Theory_Kind   => EW_Module,
                                   Clone_Kind    => EW_Export,
                                   Origin        => Pick_Clone,
                                   Substitutions => Compute_Clone_Subst));
   end Declare_Scalar_Type;

   ------------------------------
   -- Define_Scalar_Attributes --
   ------------------------------

   procedure Define_Scalar_Attributes
     (Theory     : W_Theory_Declaration_Id;
      Base_Type  : EW_Scalar;
      First      : W_Term_Id;
      Last       : W_Term_Id;
      Modulus    : W_Term_OId)
   is
      type Scalar_Attr is (S_First, S_Last, S_Modulus);

      type Attr_Info is record
         Attr_Id : Attribute_Id;
         Value   : W_Term_Id;
      end record;

      Attr_Values : constant array (Scalar_Attr) of Attr_Info :=
                      (S_First   => (Attribute_First, First),
                       S_Last    => (Attribute_Last, Last),
                       S_Modulus => (Attribute_Modulus, Modulus));
   begin
      for J in Attr_Values'Range loop
         if J /= S_Modulus or else Attr_Values (J).Value /= Why_Empty then
            Emit (Theory,
                  New_Function_Decl
                    (Domain      => EW_Term,
                     Name        =>
                       To_Ident (Attr_To_Why_Name (Attr_Values (J).Attr_Id)),
                     Binders     => (1 .. 0 => <>),
                     Return_Type => Why_Types (Base_Type),
                     Labels      => Name_Id_Sets.Empty_Set,
                     Def         => W_Expr_Id (Attr_Values (J).Value)));
         end if;
      end loop;
   end Define_Scalar_Attributes;

end Why.Gen.Scalars;
