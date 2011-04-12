------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - A R R A Y S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute it and/or modify it   --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Uintp;              use Uintp;
with Gnat2Why.Locs;      use Gnat2Why.Locs;
with Why.Conversions;    use Why.Conversions;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Axioms;     use Why.Gen.Axioms;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Preds;      use Why.Gen.Preds;
with Why.Gen.Progs;      use Why.Gen.Progs;
with Why.Gen.Terms;      use Why.Gen.Terms;

package body Why.Gen.Arrays is

   -----------------------------------
   -- Declare_Ada_Constrained_Array --
   -----------------------------------

   procedure Declare_Ada_Constrained_Array
     (File      : W_File_Id;
      Name      : String;
      Index     : String;
      Component : String)
   is
   begin
      New_Abstract_Type (File, Name);

      New_Logic
        (File => File,
         Name => Array_Access_Name (Name),
         Args =>
            (1 => New_Abstract_Type (Name => New_Identifier (Index)),
             2 => New_Abstract_Type (Name => New_Identifier (Name))),
         Return_Type =>
            New_Abstract_Type (Name => New_Identifier (Component)));

      New_Logic
        (File => File,
         Name => Array_Update_Name (Name),
         Args =>
            (1 => New_Abstract_Type (Name => New_Identifier (Index)),
             2 => New_Abstract_Type (Name => New_Identifier (Name)),
             3 => New_Abstract_Type (Name => New_Identifier (Component))),
         Return_Type => New_Abstract_Type (Name => New_Identifier (Name)));

      Define_Array_Eq_Axiom
         (File => File,
          Type_Name => Name,
          Index_Type => New_Abstract_Type (Name => New_Identifier (Index)),
          Component_Type =>
            New_Abstract_Type (Name => New_Identifier (Component)));
      Define_Array_Neq_Axiom
         (File => File,
          Type_Name => Name,
          Index_Type => New_Abstract_Type (Name => New_Identifier (Index)),
          Component_Type =>
            New_Abstract_Type (Name => New_Identifier (Component)));
   end Declare_Ada_Constrained_Array;

   -------------------------------------
   -- Declare_Ada_Unconstrained_Array --
   -------------------------------------

   procedure Declare_Ada_Unconstrained_Array
     (File      : W_File_Id;
      Name      : String;
      Index     : String;
      Component : String)
   is
      function New_Binder (Arg, Arg_Type : String) return W_Binder_Id;
      --  Return a binder with the given argument name and argument type.

      function New_Binder (Arg : String; Arg_Type : W_Value_Type_Id)
         return W_Binder_Id;
      --  Return a binder with the given argument name and argument type.

      function New_Forall (Arg, Arg_Type : String; Pred : W_Predicate_Id)
         return W_Predicate_Id;
      --  Quantify the input predicate over the given argument of the given
      --  type.

      function To_Int (T : W_Term_Id) return W_Term_Id;
      --  Convert a term of "index" type to an "int"

      ----------------
      -- New_Binder --
      ----------------

      function New_Binder (Arg, Arg_Type : String) return W_Binder_Id
      is
      begin
         return
            New_Binder
               (Names => (1 => New_Identifier (Arg)),
                Arg_Type =>
                  New_Abstract_Type (Name => New_Identifier (Arg_Type)));
      end New_Binder;

      function New_Binder (Arg : String; Arg_Type : W_Value_Type_Id)
         return W_Binder_Id
      is
      begin
         return
            New_Binder
               (Names => (1 => +New_Identifier (Arg)),
                Arg_Type => Arg_Type);
      end New_Binder;

      ----------------
      -- New_Forall --
      ----------------

      function New_Forall (Arg, Arg_Type : String; Pred : W_Predicate_Id)
         return W_Predicate_Id
      is
      begin
         return
            New_Universal_Quantif
               (Variables => (1 => New_Identifier (Arg)),
                Var_Type  =>
                  New_Abstract_Type (Name => New_Identifier (Arg_Type)),
                Pred      => Pred);
      end New_Forall;

      ------------
      -- To_Int --
      ------------

      function To_Int (T : W_Term_Id) return W_Term_Id
      is
      begin
         return
            New_Operation
               (Name       => New_Conversion_To_Int (Index),
                Parameters => (1 => T));
      end To_Int;

      --  Beginning of processing for Declare_Ada_Unconstrained_Array

   begin
      Declare_Ada_Constrained_Array (File, Name, Index, Component);

      --  Define accessors for 'First and 'Last
      New_Logic
        (File => File,
         Name => Array_First_Name (Name),
         Args =>
            (1 => New_Abstract_Type (Name => New_Identifier (Name))),
         Return_Type => New_Abstract_Type (Name => New_Identifier (Index)));
      New_Logic
        (File => File,
         Name => Array_Last_Name (Name),
         Args =>
            (1 => New_Abstract_Type (Name => New_Identifier (Name))),
         Return_Type => New_Abstract_Type (Name => New_Identifier (Index)));

      --  Declare parameters with preconditions for access and update
      declare
         --  Common declarations for access & update
         Arg_A  : constant String := "a";
         Arg_I  : constant String := "i";
         Arg_V  : constant String := "v";
         First         : constant W_Term_Id :=
            New_Operation
              (Name => Array_First_Name (Name),
               Parameters => (1 => New_Term (Arg_A)));
         First_Int     : constant W_Term_Id := To_Int (First);
         Last          : constant W_Term_Id :=
            New_Operation
              (Name => Array_Last_Name (Name),
               Parameters => (1 => New_Term (Arg_A)));
         Last_Int      : constant W_Term_Id := To_Int (Last);
         Length         : constant W_Term_Id :=
            New_Operation
              (Name => Array_Length_Name (Name),
               Parameters => (1 => New_Term (Arg_A)));
         Length_Int     : constant W_Term_Id := To_Int (Length);
         Pre : constant W_Predicate_Id :=
            New_Related_Terms
               (Left   => First_Int,
                Op     => New_Rel_Le,
                Right  =>
                  To_Int (New_Term (Arg_I)),
                Op2    => New_Rel_Le,
                Right2 => Last_Int);
         Binders_Update : constant W_Binder_Array :=
            (1 => New_Binder (Arg_I, Index),
             2 =>
               New_Binder
                (Arg_A,
                 New_Ref_Type
                     (Aliased_Type =>
                        New_Abstract_Type (Name => New_Identifier (Name)))),
             3 => New_Binder (Arg_V, Component));
         Binders_Access : constant W_Binder_Array :=
            (1 => New_Binder (Arg_I, Index),
             2 => New_Binder (Arg_A, Name));
         Logic_Update_Term : constant W_Term_Id :=
            New_Array_Update_Term
               (Type_Name => Name,
                Ar        => New_Old_Ident (New_Identifier (Arg_A)),
                Index     => New_Term (Arg_I),
                Value     => New_Term (Arg_V));
         Post_Update : constant W_Predicate_Id :=
            New_Equal (New_Term (Arg_A), Logic_Update_Term);
         Post_Access : constant W_Predicate_Id :=
            New_Equal
               (Left => New_Result_Identifier,
                Right =>
                  New_Array_Access_Term
                     (Type_Name => Name,
                      Ar        => New_Old_Ident (New_Identifier (Arg_A)),
                      Index     => New_Term (Arg_I)));
         Normal_Length : constant W_Term_Id :=
            --  'last - 'first + 1
            New_Arith_Operation
               (Left =>
                  New_Arith_Operation
                     (Left => +Duplicate_Any_Node (Id => +Last_Int),
                      Op => New_Op_Substract,
                      Right => +Duplicate_Any_Node (Id => +First_Int)),
                Op => New_Op_Add,
                Right => New_Integer_Constant (Value => Uint_1));
         Non_Zero_Pred : constant W_Predicate_Id :=
            --  'last  >= 'first => 'length = 'last - 'first + 1
            New_Implication
              (Left =>
                 New_Related_Terms
                   (Left => +Duplicate_Any_Node (Id => +Last_Int),
                    Op => New_Rel_Ge,
                    Right => +Duplicate_Any_Node (Id => +First_Int)),
               Right => New_Equal (Length_Int, Normal_Length));
         Zero_Pred     : constant W_Predicate_Id :=
            New_Implication
              (Left =>
                 New_Related_Terms
                   (Left => +Duplicate_Any_Node (Id => +Last_Int),
                    Op => New_Rel_Lt,
                    Right => +Duplicate_Any_Node (Id => +First_Int)),
               Right =>
                  New_Equal
                     (+Duplicate_Any_Node (Id => +Length_Int),
                      New_Integer_Constant (Value => Uint_0)));

         procedure Update_Equal_Axiom
            (File       : W_File_Id;
             Axiom_Name : W_Identifier_Id;
             Attr_Name  : W_Identifier_Id;
             Left       : W_Term_Id);
         --  Generate an axiom that states that the attribute "attr_name"
         --  remains unchanged on array update.

         ------------------------
         -- Update_Equal_Axiom --
         ------------------------

         procedure Update_Equal_Axiom
            (File       : W_File_Id;
             Axiom_Name : W_Identifier_Id;
             Attr_Name  : W_Identifier_Id;
             Left       : W_Term_Id)
         is
            Right : constant W_Term_Id :=
               New_Operation
                  (Name       => Attr_Name,
                   Parameters =>
                     (1 =>
                        New_Array_Update_Term
                           (Type_Name => Name,
                            Ar        => New_Term (Arg_A),
                            Index     => New_Term (Arg_I),
                            Value     => New_Term (Arg_V))));
         begin
            New_Axiom
               (File => File,
                Name => Axiom_Name,
                Axiom_Body =>
                  New_Forall
                    (Arg_A, Name,
                     New_Forall
                       (Arg_I, Index,
                        New_Forall
                           (Arg_V, Component,
                            New_Equal (Left, Right)))));
         end Update_Equal_Axiom;

      begin
         --  Declaration for update parameter
         New_Parameter
            (File        => File,
             Name        => To_Program_Space (Array_Update_Name (Name)),
             Binders     => Binders_Update,
             Return_Type => New_Type_Unit,
             Effects     =>
               New_Effects (Writes => (1 => New_Identifier (Arg_A))),
             Pre         => New_Assertion (Pred => Pre),
             Post        => New_Assertion (Pred => Post_Update));
         --  Declaration for access parameter
         New_Parameter
            (File        => File,
             Name        => To_Program_Space (Array_Access_Name (Name)),
             Binders     => Binders_Access,
             Return_Type =>
               New_Abstract_Type (Name => New_Identifier (Component)),
             Pre         =>
               New_Assertion (Pred => +Duplicate_Any_Node (Id => +Pre)),
             Post        => New_Assertion (Pred => Post_Access));
         --  Define accessor for 'Length, with axioms
         New_Logic
           (File => File,
            Name => Array_Length_Name (Name),
            Args =>
               (1 => New_Abstract_Type (Name => New_Identifier (Name))),
            Return_Type =>
               New_Abstract_Type (Name => New_Identifier (Index)));
         New_Axiom
            (File => File,
             Name => Array_Length_Non_Zero (Name),
             Axiom_Body =>
               New_Universal_Quantif
                 (Variables => (1 => New_Identifier (Arg_A)),
                  Var_Type =>
                     New_Abstract_Type (Name => New_Identifier (Name)),
                  Pred => Non_Zero_Pred));
         New_Axiom
            (File => File,
             Name => Array_Length_Zero (Name),
             Axiom_Body =>
               New_Universal_Quantif
                 (Variables => (1 => New_Identifier (Arg_A)),
                  Var_Type =>
                     New_Abstract_Type (Name => New_Identifier (Name)),
                  Pred => Zero_Pred));
         --  Define axioms that state that 'First, 'Last, 'Length are not
         --  modified by update
         Update_Equal_Axiom
            (File,
             Array_First_Update (Name),
             Array_First_Name (Name),
             +Duplicate_Any_Node (Id => +First));
         Update_Equal_Axiom
            (File,
             Array_Last_Update (Name),
             Array_Last_Name (Name),
             +Duplicate_Any_Node (Id => +Last));
         Update_Equal_Axiom
            (File,
             Array_Length_Update (Name),
             Array_Length_Name (Name),
             +Duplicate_Any_Node (Id => +Length));
      end;
   end Declare_Ada_Unconstrained_Array;

   ---------------------------
   -- New_Array_Access_Prog --
   ---------------------------

   function New_Array_Access_Prog
     (Ada_Node      : Node_Id;
      Type_Name     : String;
      Ar            : W_Prog_Id;
      Index         : W_Prog_Id;
      Unconstrained : Boolean) return W_Prog_Id
   is
      Name : constant W_Identifier_Id := Array_Access_Name (Type_Name);
   begin
      if Unconstrained then
         return
           New_Located_Call
             (Ada_Node => Ada_Node,
              Name     => To_Program_Space (Name),
              Progs    => (1 => Index, 2 => Ar),
              Reason   => VC_Array_Bounds_Check);
      else
         return
           New_Prog_Call
             (Name => Name,
              Progs => (1 => Index, 2 => Ar));
      end if;
   end New_Array_Access_Prog;

   ---------------------------
   -- New_Array_Access_Term --
   ---------------------------

   function New_Array_Access_Term
     (Type_Name : String;
      Ar : W_Term_Id;
      Index : W_Term_Id) return W_Term_Id is
   begin
      return
        New_Operation
          (Name => Array_Access_Name (Type_Name),
           Parameters => (1 => Index, 2 => Ar));
   end New_Array_Access_Term;

   ---------------------------
   -- New_Array_Update_Prog --
   ---------------------------

   function New_Array_Update_Prog
      (Ada_Node      : Node_Id;
       Type_Name     : String;
       Ar            : W_Identifier_Id;
       Index         : W_Prog_Id;
       Value         : W_Prog_Id;
       Unconstrained : Boolean) return W_Prog_Id
   is
      Name : constant W_Identifier_Id := Array_Update_Name (Type_Name);
   begin
      if Unconstrained then
         return
            New_Located_Call
               (Ada_Node => Ada_Node,
                Name     => To_Program_Space (Name),
                Progs    =>
                  (1 => Index,
                   2 => New_Prog_Identifier (Def => Ar),
                   3 => Value),
                Reason   => VC_Array_Bounds_Check);
      else
         return
            New_Assignment
              (Name => +Duplicate_Identifier (Id => +Ar),
               Value =>
                  New_Prog_Call
                    (Name => Name,
                     Progs =>
                      (1 => Index,
                       2 => New_Deref (Ref => Ar),
                       3 => Value)));
      end if;
   end New_Array_Update_Prog;

   ---------------------------
   -- New_Array_Update_Term --
   ---------------------------

   function New_Array_Update_Term
      (Type_Name : String;
       Ar        : W_Term_Id;
       Index     : W_Term_Id;
       Value     : W_Term_Id) return W_Term_Id
   is
   begin
      return
        New_Operation
          (Name => Array_Update_Name (Type_Name),
           Parameters => (1 => Index, 2 => Ar, 3 => Value));
   end New_Array_Update_Term;

end Why.Gen.Arrays;
