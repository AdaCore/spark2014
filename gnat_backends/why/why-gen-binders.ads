------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - B I N D E R S                       --
--                                                                          --
--                                 S p e c                                  --
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

with Types;              use Types;
pragma Warnings (Off);
--  ??? Why.Types" is directly visible as "Types", as it has "Why" as a
--  common ancestor with the current package. So it hides compilation unit
--  with the same name ("Types"). Maybe we should think of renaming it to
--  "Why.W_Types".
with Why.Types;          use Why.Types;
pragma Warnings (On);
with Why.Sinfo;          use Why.Sinfo;
with Why.Ids;            use Why.Ids;
with Why.Atree.Builders; use Why.Atree.Builders;

package Why.Gen.Binders is
   --  This package provides operations to build binders in program space
   --  and in logic space.

   type Modifier_Type is (Array_Modifier, Ref_Modifier, None);

   type Binder_Type is record
      Ada_Node : Node_Id := Empty;
      B_Name   : W_Identifier_Id;
      B_Type   : W_Primitive_Type_Id;
      Modifier : Modifier_Type := None;
   end record;

   type Binder_Array is array (Positive range <>) of Binder_Type;

   function New_Universal_Quantif
     (Ada_Node : Node_Id := Empty;
      Binders  : Binder_Array;
      Pred     : W_Predicate_Id)
     return W_Predicate_Id;

   function New_Existential_Quantif
     (Ada_Node : Node_Id := Empty;
      Binders  : Binder_Array;
      Pred     : W_Predicate_Id)
     return W_Predicate_Id;

   function New_Call_To_Logic
     (Ada_Node : Node_Id := Empty;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array)
     return W_Term_Id;

   --  Top-level entities

   function New_Logic
     (Ada_Node    : Node_Id := Empty;
      Name        : W_Identifier_Id;
      Binders     : Binder_Array;
      Return_Type : W_Primitive_Type_Id)
     return W_Logic_Declaration_Class_Id;

   function New_Function
     (Ada_Node    : Node_Id := Empty;
      Name        : W_Identifier_Id;
      Binders     : Binder_Array;
      Return_Type : W_Primitive_Type_Id;
      Def         : W_Term_Id)
     return W_Logic_Declaration_Class_Id;

   function New_Predicate_Definition
     (Ada_Node : Node_Id := Empty;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array;
      Def      : W_Predicate_Id)
     return W_Logic_Declaration_Class_Id;

   function New_Global_Binding
     (Ada_Node : Node_Id := Empty;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array;
      Pre      : W_Predicate_Id := New_True_Literal_Pred;
      Def      : W_Prog_Id;
      Post     : W_Predicate_Id := New_True_Literal_Pred)
     return W_Declaration_Id;

   function New_Parameter
     (Ada_Node    : Node_Id := Empty;
      Name        : W_Identifier_Id;
      Binders     : Binder_Array;
      Return_Type : W_Primitive_Type_Id;
      Effects     : W_Effects_Id := New_Effects;
      Pre         : W_Predicate_Id := New_True_Literal_Pred;
      Post        : W_Predicate_Id := New_True_Literal_Pred)
     return W_Declaration_Id;

   function New_Guarded_Axiom
     (Ada_Node : Node_Id := Empty;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array;
      Pre      : W_Predicate_OId := Why_Empty;
      Def      : W_Predicate_Id)
     return W_Logic_Declaration_Class_Id;
   --  generate an axiom of the form:
   --
   --   axiom <name>:
   --    forall x1 ... xn.
   --       pre -> <def>

   function New_Defining_Axiom
     (Ada_Node : Node_Id := Empty;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array;
      Pre      : W_Predicate_OId := Why_Empty;
      Def      : W_Term_Id)
     return W_Logic_Declaration_Class_Id;
   --  generate an axiom of the form:
   --
   --   axiom <name>___def:
   --    forall x1 ... xn.
   --       pre -> (<name> (x1 .. xn) = <def>)

   function New_Defining_Bool_Axiom
     (Ada_Node : Node_Id := Empty;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array;
      Pre      : W_Predicate_Id := Why_Empty;
      Def      : W_Predicate_Id)
     return W_Logic_Declaration_Class_Id;
   --  Same as new_defining_axiom, but for functions returning booleans.
   --  (for those, predicates are generated instead of logics).

   subtype W_Binded_Declaration is Why_Node_Kind
     with Predicate => (W_Binded_Declaration in W_Unused_At_Start
                        | W_Logic
                        | W_Function
                        | W_Predicate_Definition
                        | W_Parameter_Declaration
                        | W_Global_Binding);

   type Declaration_Spec (Kind : W_Binded_Declaration := W_Unused_At_Start) is
     record
        Name : W_Identifier_OId := Why_Empty;
        --  Name of the entity to declare. If not specified, a defaut is
        --  given following the defaut naming convention.

        Pre  : W_Predicate_OId := Why_Empty;
        Post : W_Predicate_OId := Why_Empty;

        case Kind is
           when W_Logic | W_Function =>
              Term : W_Term_OId := Why_Empty;

           when W_Predicate_Definition =>
              Pred : W_Predicate_Id;

           when W_Global_Binding =>
              Prog : W_Prog_Id;

           when W_Parameter_Declaration =>
              Effects  : W_Effects_Id := New_Effects;

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

           when others =>
              --  Invalid
              null;
        end case;
     end record;

   type Declaration_Spec_Array is array (Positive range <>)
     of Declaration_Spec;

   procedure Emit_Top_Level_Declarations
     (File        : W_File_Id;
      Ada_Node    : Node_Id := Empty;
      Name        : W_Identifier_Id;
      Binders     : Binder_Array;
      Return_Type : W_Primitive_Type_Id;
      Spec        : in out Declaration_Spec_Array);

end Why.Gen.Binders;
