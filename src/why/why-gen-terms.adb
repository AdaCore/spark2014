------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - G E N - T E R M S                    --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2021, AdaCore                     --
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

with SPARK_Atree;           use SPARK_Atree;
with SPARK_Atree.Entities;  use SPARK_Atree.Entities;
with Types;                 use Types;
with Why.Atree.Accessors;   use Why.Atree.Accessors;
with Why.Atree.Modules;     use Why.Atree.Modules;
with Why.Atree.Traversal;   use Why.Atree.Traversal;
with Why.Conversions;       use Why.Conversions;
with Why.Gen.Expr;          use Why.Gen.Expr;

package body Why.Gen.Terms is

   ---------------------
   -- Has_Dereference --
   ---------------------

   function Has_Dereference (W : Why_Node_Id) return Boolean is
      type Collect_State is new Traversal_State with record
         Found : Boolean;
      end record;

      procedure Deref_Pre_Op
        (State : in out Collect_State;
         Node  : W_Deref_Id);

      ------------------
      -- Deref_Pre_Op --
      ------------------

      procedure Deref_Pre_Op
        (State : in out Collect_State;
         Node  : W_Deref_Id) is
         pragma Unreferenced (Node);
      begin
         State.Found   := True;
         State.Control := Terminate_Immediately;
      end Deref_Pre_Op;

      SS : Collect_State :=
        (Control => Continue, Found => False);

   --  Start of processing for Has_Dereference

   begin
      Traverse (SS, W);
      return SS.Found;
   end Has_Dereference;

   ------------------------------------
   -- Has_Dereference_Or_Any_Or_Self --
   ------------------------------------

   function Has_Dereference_Or_Any_Or_Self (T : W_Term_Id) return Boolean is
      type Search_State is new Traversal_State with record
         Found : Boolean;
      end record;

      procedure Deref_Pre_Op
        (State : in out Search_State;
         Node  : W_Deref_Id);

      procedure Binding_Ref_Pre_Op
        (State : in out Search_State;
         Node  : W_Binding_Ref_Id);

      procedure Any_Expr_Pre_Op
        (State : in out Search_State;
         Node  : W_Any_Expr_Id);

      procedure Identifier_Pre_Op
        (State : in out Search_State;
         Node  : W_Identifier_Id);
      --  Search for occurrences of the "self" special parameter of protected
      --  subprograms, which can be identified by its Ada_Node pointing to the
      --  corresponding protected type.

      ------------------
      -- Deref_Pre_Op --
      ------------------

      procedure Deref_Pre_Op
        (State : in out Search_State;
         Node  : W_Deref_Id)
      is
         pragma Unreferenced (Node);
      begin
         State.Found   := True;
         State.Control := Terminate_Immediately;
      end Deref_Pre_Op;

      ------------------------
      -- Binding_Ref_Pre_Op --
      ------------------------

      procedure Binding_Ref_Pre_Op
        (State : in out Search_State;
         Node  : W_Binding_Ref_Id)
      is
         pragma Unreferenced (Node);
      begin
         State.Found   := True;
         State.Control := Terminate_Immediately;
      end Binding_Ref_Pre_Op;

      ---------------------
      -- Any_Expr_Pre_Op --
      ---------------------

      procedure Any_Expr_Pre_Op
        (State : in out Search_State;
         Node  : W_Any_Expr_Id)
      is
         pragma Unreferenced (Node);
      begin
         State.Found   := True;
         State.Control := Terminate_Immediately;
      end Any_Expr_Pre_Op;

      -----------------------
      -- Identifier_Pre_Op --
      -----------------------

      procedure Identifier_Pre_Op
        (State : in out Search_State;
         Node  : W_Identifier_Id)
      is
         N : constant Node_Id := Get_Ada_Node (+Node);
      begin
         if Nkind (N) in N_Entity
           and then Is_Protected_Type (N)
         then
            State.Found   := True;
            State.Control := Terminate_Immediately;
         else
            State.Control := Abandon_Children;
         end if;
      end Identifier_Pre_Op;

      SS : Search_State := (Control => Continue, Found => False);

   --  Start of Processing for Has_Dereference_Or_Any

   begin
      Traverse (SS, +T);
      return SS.Found;
   end Has_Dereference_Or_Any_Or_Self;

   -------------
   -- New_Old --
   -------------

   function New_Old (Expr : W_Expr_Id; Domain : EW_Domain) return W_Expr_Id
   is
   begin
      return New_Tagged (Ada_Node => Get_Ada_Node (+Expr),
                         Def      => Expr,
                         Tag      => Old_Tag,
                         Domain   => Domain,
                         Typ      => Get_Type (Expr));
   end New_Old;

end Why.Gen.Terms;
