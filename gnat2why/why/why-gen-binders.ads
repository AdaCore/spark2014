------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - B I N D E R S                       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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

with Types;                  use Types;
with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;
pragma Warnings (Off);
--  ??? Why.Types" is directly visible as "Types", as it has "Why" as a
--  common ancestor with the current package. So it hides compilation unit
--  with the same name ("Types"). Maybe we should think of renaming it to
--  "Why.W_Types".
with Why.Types;              use Why.Types;
pragma Warnings (On);
with Why.Sinfo;              use Why.Sinfo;
with Why.Ids;                use Why.Ids;
with Why.Atree.Builders;     use Why.Atree.Builders;
with Why.Gen.Preds;          use Why.Gen.Preds;

package Why.Gen.Binders is
   --  This package provides operations to build binders in program space
   --  and in logic space.

   type Modifier_Type is (Array_Modifier, Ref_Modifier, None);

   type Binder_Type is record
      Ada_Node : Node_Id := Empty;
      B_Name   : W_Identifier_Id;
      B_Ent    : Entity_Name;
      B_Type   : W_Type_Id;
      Mutable  : Boolean := False;
   end record;
   --  This record represents a variable binding B_Name of type B_Type. In some
   --  cases, extra information is stored concerning the Ada entity that is
   --  represented by this binder. The Ada_Node may be used for that, or the
   --  B_Ent field if no entity node is available for the entity.

   type Binder_Array is array (Positive range <>) of Binder_Type;

   function New_Binders
     (Anonymous_Binders : W_Type_Array)
     return Binder_Array;

   function New_Universal_Quantif
     (Ada_Node : Node_Id := Empty;
      Binders  : Binder_Array;
      Triggers : W_Triggers_OId := Why_Empty;
      Pred     : W_Pred_Id)
     return W_Pred_Id;

   function New_Existential_Quantif
     (Ada_Node : Node_Id := Empty;
      Binders  : Binder_Array;
      Pred     : W_Pred_Id)
     return W_Pred_Id;

   function New_Call
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array)
     return W_Expr_Id;
   --  Create a call to an operation in the given domain with parameters
   --  taken from Binders. Typically, from:
   --
   --     (x1 : type1) (x2 : type2)
   --
   --  ...it produces:
   --
   --     operation_name (x1, x2)

   --  Top-level entities

   function New_Function_Decl
     (Ada_Node    : Node_Id := Empty;
      Domain      : EW_Domain;
      Name        : W_Identifier_Id;
      Binders     : Binder_Array;
      Return_Type : W_Type_Id;
      Labels      : W_Identifier_Array := (1 .. 0 => <>);
      Effects     : W_Effects_Id := New_Effects;
      Pre         : W_Pred_Id := True_Pred;
      Post        : W_Pred_Id := True_Pred)
     return W_Declaration_Id;

   function New_Function_Def
     (Ada_Node    : Node_Id := Empty;
      Domain      : EW_Domain;
      Name        : W_Identifier_Id;
      Binders     : Binder_Array;
      Return_Type : W_Type_OId := Why_Empty;
      Def         : W_Expr_Id;
      Labels      : W_Identifier_Array := (1 .. 0 => <>);
      Pre         : W_Pred_Id := True_Pred;
      Post        : W_Pred_Id := True_Pred)
     return W_Declaration_Id;

   function New_Record_Definition
      (Ada_Node : Node_Id := Empty;
       Name     : W_Identifier_Id;
       Binders  : Binder_Array) return W_Declaration_Id;

   function New_Guarded_Axiom
     (Ada_Node : Node_Id := Empty;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array;
      Triggers : W_Triggers_OId := Why_Empty;
      Pre      : W_Pred_OId := Why_Empty;
      Def      : W_Pred_Id)
     return W_Declaration_Id;
   --  generate an axiom of the form:
   --
   --   axiom <name>:
   --    forall x1 ... xn.
   --       pre -> <def>

   function New_Defining_Axiom
     (Ada_Node    : Node_Id := Empty;
      Name        : W_Identifier_Id;
      Binders     : Binder_Array;
      Return_Type : EW_Type;
      Ada_Type    : Entity_Id := Empty;
      Pre         : W_Pred_OId := Why_Empty;
      Def         : W_Term_Id)
     return W_Declaration_Id;
   --  generate an axiom of the form:
   --
   --   axiom <name>___def:
   --    forall x1 ... xn.
   --       pre -> (<name> (x1 .. xn) = <def>)

   --  Ada_Type is the Ada entity of the return type. If it is a scalar type,
   --  the comparison is done in the Why base type, and we expect "def" to be
   --  of the base type.

   function New_Defining_Bool_Axiom
     (Ada_Node : Node_Id := Empty;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array;
      Pre      : W_Pred_Id := Why_Empty;
      Def      : W_Pred_Id)
     return W_Declaration_Id;
   --  Same as new_defining_axiom, but for functions returning booleans.
   --  (for those, predicates are generated instead of logics).

   subtype W_Binded_Declaration is Why_Node_Kind range
     W_Function_Decl ..
     W_Function_Def;

   type Declaration_Spec
     (Kind   : W_Binded_Declaration := W_Function_Def;
      Domain : EW_Domain            := EW_Prog) is
     record
        Name : W_Identifier_OId := Why_Empty;
        --  Name of the entity to declare. If not specified, a defaut is
        --  given following the defaut naming convention.

        Pre  : W_Pred_OId := Why_Empty;

        Label : W_Identifier_OId := Why_Empty;

        Post : W_Pred_OId := Why_Empty;
        --  If no postcondition is given, and if a logic declaration
        --  is provided, one will be generated that will use this
        --  logic declaration. e.g. if Name is "my_func" and Binders is:
        --
        --     (x1 : type1) -> (x2 : type2)
        --
        --  ...then the logic declaration will be:
        --
        --     logic my_func : type1, type2 -> type3
        --
        --  ...and the generated program-space declaration, with the
        --  default postcondition will be:
        --
        --     parameter my_func_ :
        --      x1 : type1 -> x2 : type2 ->
        --     { pre }
        --      type3
        --     { my_func (x1, x2) = result }

        case Kind is
           when W_Function_Def =>
              case Domain is
                 when EW_Prog =>
                    Prog : W_Prog_Id;

                 when EW_Term =>
                    Term : W_Term_Id;

                 when EW_Pred =>
                    Pred : W_Pred_Id;
              end case;

           when W_Function_Decl =>
              case Domain is
                 when EW_Prog =>
                    Effects   : W_Effects_Id := New_Effects;

                 when EW_Term =>
                    Def : W_Term_OId := Why_Empty;

                 when EW_Pred =>
                    null;
              end case;
        end case;
     end record;

   type Declaration_Spec_Array is array (Positive range <>)
     of Declaration_Spec;

   procedure Set_Top_Level_Declarations
     (Theory      : W_Theory_Declaration_Id;
      Ada_Node    : Node_Id := Empty;
      Binders     : Binder_Array;
      Return_Type : W_Type_Id;
      Spec        : in out Declaration_Spec_Array);

   procedure Emit_Top_Level_Declarations
     (Theory      : W_Theory_Declaration_Id;
      Ada_Node    : Node_Id := Empty;
      Binders     : Binder_Array;
      Return_Type : W_Type_Id;
      Spec        : Declaration_Spec_Array);

   function Unit_Param return Binder_Type;
   --  return a dummy binder for a single argument of type unit

end Why.Gen.Binders;
