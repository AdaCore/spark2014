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

with VC_Kinds;           use VC_Kinds;
with Why.Conversions;    use Why.Conversions;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Preds;      use Why.Gen.Preds;
with Why.Gen.Progs;      use Why.Gen.Progs;
with Why.Gen.Terms;      use Why.Gen.Terms;
with Why.Gen.Binders;    use Why.Gen.Binders;

package body Why.Gen.Arrays is

   -----------------------------------
   -- Declare_Ada_Constrained_Array --
   -----------------------------------

   procedure Declare_Ada_Constrained_Array
     (File      : W_File_Id;
      Name      : String;
      Component : String;
      First     : Uint;
      Last      : Uint)
   is
      Ar         : constant W_Term_Id :=
                     New_Term ("a");
      Ar_Binder  : constant Binder_Type :=
                     (B_Name => New_Identifier ("a"),
                      B_Type =>
                        New_Abstract_Type (Name => (New_Identifier (Name))),
                      others => <>);
   begin
      Declare_Ada_Unconstrained_Array (File, Name, Component);

      --  State axioms about fixed 'First, 'Last and 'Length

      Emit
        (File,
         New_Guarded_Axiom
           (Name => Array_First_Static.Id (Name),
            Binders => (1 => Ar_Binder),
            Def =>
              New_Equal
                (New_Array_First_Term (Name, Ar),
                 New_Integer_Constant (Value => First))));
      Emit
        (File,
         New_Guarded_Axiom
           (Name => Array_Last_Static.Id (Name),
            Binders => (1 => Ar_Binder),
            Def =>
              New_Equal
                (New_Array_Last_Term (Name, Ar),
                 New_Integer_Constant (Value => Last))));
      Emit
        (File,
         New_Guarded_Axiom
           (Name => Array_Length_Static.Id (Name),
            Binders => (1 => Ar_Binder),
            Def =>
              New_Equal
                (New_Array_Length_Term (Name, Ar),
                 New_Integer_Constant
                   (Value => UI_Add (UI_Sub (Last, First), 1)))));
   end Declare_Ada_Constrained_Array;

   -------------------------------------
   -- Declare_Ada_Unconstrained_Array --
   -------------------------------------

   procedure Declare_Ada_Unconstrained_Array
     (File      : W_File_Id;
      Name      : String;
      Component : String)
   is
      Comp_Type  : constant W_Primitive_Type_Id :=
         New_Abstract_Type (Name => (New_Identifier (Component)));
      Ar_Type    : constant W_Primitive_Type_Id :=
         New_Generic_Actual_Type_Chain
            (Type_Chain => (1 => Comp_Type),
             Name => New_Identifier (Ada_Array));
      Name_Type  : constant W_Primitive_Type_Id :=
         New_Abstract_Type (Name => (New_Identifier (Name)));
      Ar         : constant W_Term_Id :=
         New_Term ("a");
      Arb        : constant W_Term_Id :=
         New_Term ("b");
      Ar_Binder_2 : constant Binder_Type :=
                      (B_Name => New_Identifier ("a"),
                       B_Type => Ar_Type,
                       others => <>);
   begin
      --  generate the theory:
      --  type t
      --  logic to_ : t -> comp ada_array
      --  logic from_ : comp ada_array -> t
      --  axiom 1 : forall x, to_ (from_ (x)) = x
      --  axiom 2 : forall x, y, to_ (x) = to_ (y) -> x = y
      New_Abstract_Type (File, Name);
      New_Logic
         (File,
          Array_Conv_From.Id (Name),
          Args => (1 => +Name_Type),
          Return_Type => +Ar_Type);
      Emit
        (File,
         New_Logic
           (Name => Array_Conv_To.Id (Name),
            Binders => (1 => Ar_Binder_2),
            Return_Type => Name_Type));
      New_Axiom
         (File       => File,
          Name       => Array_Conv_Idem.Id (Name),
          Axiom_Body =>
            New_Universal_Quantif
              (Var_Type  => New_Abstract_Type (Name =>
                                                 (New_Identifier (Name))),
               Variables => (1 => New_Identifier ("a")),
               Triggers  => New_Triggers (
                 Triggers => (1 =>
                                New_Trigger (
                                  Terms => (1 => New_Operation
                                            (Name => Array_Conv_From.Id (Name),
                                             Parameters => (1 => Ar)))))),
               Pred      =>
                 New_Equal
                   (Ar,
                    New_Operation
                      (Name       => Array_Conv_To.Id (Name),
                       Parameters =>
                         (1 => New_Operation
                            (Name => Array_Conv_From.Id (Name),
                             Parameters => (1 => Ar)))))));
      Emit
        (File,
         New_Guarded_Axiom
           (Name => Array_Conv_Idem_2.Id (Name),
            Binders => (1 => Ar_Binder_2),
            Def =>
              New_Universal_Quantif
                (Var_Type  => +Ar_Type,
                 Variables => (1 => New_Identifier ("b")),
                 Triggers  => New_Triggers (
                   Triggers =>
                     (1 =>
                        New_Trigger (
                          Terms => (1 => New_Operation
                                    (Name => Array_Conv_To.Id (Name),
                                     Parameters => (1 => Ar)),
                                    2 => New_Operation
                                      (Name => Array_Conv_To.Id (Name),
                                       Parameters => (1 => Arb)))))),
                 Pred      =>
                   New_Implication
                     (Left  => New_Equal
                          (New_Operation
                               (Name => Array_Conv_To.Id (Name),
                                Parameters => (1 => Ar)),
                           New_Operation
                             (Name => Array_Conv_To.Id (Name),
                              Parameters => (1 => Arb))),
                      Right => New_Equal (Ar, Arb)))));
   end Declare_Ada_Unconstrained_Array;

   --------------------------------
   -- Declare_Generic_Array_Type --
   --------------------------------

   procedure Declare_Generic_Array_Type (File : W_File_Id)
   is
      A       : constant W_Primitive_Type_Id :=
         New_Generic_Formal_Type (Name => New_Identifier ("a"));
      Ar_Type : constant W_Primitive_Type_Id :=
         New_Generic_Actual_Type_Chain
            (Type_Chain => (1 => A),
             Name => New_Identifier (Ada_Array));
   begin

      --  declare all the symbols:
      --    type 'a t
      --    logic access : int , 'a t -> 'a
      --    logic update : int, 'a t, 'a  -> 'a t
      --    logic length : 'a t -> int
      --    logic first : 'a t -> int
      --    logic last : 'a t -> int
      --    parameter access_ : (i : int) -> (a : 'a t) ->
      --       { first (a) <= i <= last (a)  } 'a { result = access (i,a) }
      --    parameter update_ : (i : int) -> (a : 'a t) -> (v : 'a)
      --       { first (a) <= i <= last (a)  } 'a t { result = update (i,a,v) }

      New_Abstract_Type (File, New_Identifier (Ada_Array), 1);
      New_Logic
        (File,
         Array_Access_Name.Id (Ada_Array),
         Args =>
            (1 => New_Type_Int,
             2 => +Ar_Type),
         Return_Type => +A);
      New_Logic
        (File,
         Array_Update_Name.Id (Ada_Array),
         Args =>
            (1 => New_Type_Int,
             2 => +Ar_Type,
             3 => +A),
         Return_Type => +Ar_Type);
      New_Logic
        (File,
         Array_Length_Name.Id (Ada_Array),
         Args =>
            (1 => +Ar_Type),
         Return_Type => New_Type_Int);
      New_Logic
        (File,
         Array_First_Name.Id (Ada_Array),
         Args =>
            (1 => +Ar_Type),
         Return_Type => New_Type_Int);
      New_Logic
        (File,
         Array_Last_Name.Id (Ada_Array),
         Args =>
            (1 => +Ar_Type),
         Return_Type => New_Type_Int);

      --  Declare the axioms:
      --  access/update (2 axioms)
      --  length/first/last+update (3 axioms)
      --  length/first/last/zero   (2 axioms)

      declare
         Ar         : constant W_Term_Id := New_Term ("a");
         Index      : constant W_Term_Id := New_Term ("i");
         Index_Diff : constant W_Term_Id := New_Term ("j");
         Component  : constant W_Term_Id := New_Term ("v");
         Ar_Binder  : constant Binder_Type :=
                        (B_Name => New_Identifier ("a"),
                         B_Type => +Ar_Type,
                         others => <>);
         Index_Binder : constant Binder_Type :=
                          (B_Name => New_Identifier ("i"),
                           B_Type => New_Type_Int,
                           others => <>);
         Component_Binder  : constant Binder_Type :=
                               (B_Name => New_Identifier ("v"),
                                B_Type => +A,
                                others => <>);
         Index_Diff_Binder  : constant Binder_Type :=
                                (B_Name => New_Identifier ("j"),
                                 B_Type => New_Type_Int,
                                 others => <>);
         Upd_Term   : constant W_Term_Id :=
           New_Operation
             (Name => Array_Update_Name.Id (Ada_Array),
              Parameters => (1 => Index, 2 => Ar, 3 => Component));
         Get_Term : constant W_Term_Id :=
           New_Operation
             (Name => Array_Access_Name.Id (Ada_Array),
              Parameters => (1 => Index_Diff, 2 => Ar));
         First_Term : constant W_Term_Id :=
           New_Operation
             (Name => Array_First_Name.Id (Ada_Array),
              Parameters => (1 => Ar));
         Last_Term : constant W_Term_Id :=
           New_Operation
             (Name => Array_Last_Name.Id (Ada_Array),
              Parameters => (1 => Ar));
         Length_Term : constant W_Term_Id :=
           New_Operation
             (Name => Array_Length_Name.Id (Ada_Array),
              Parameters => (1 => Ar));
         Acc_Upd_Term_Eq : constant W_Term_Id :=
            New_Operation
             (Name => Array_Access_Name.Id (Ada_Array),
              Parameters => (1 => Index, 2 => Upd_Term));
         Acc_Upd_Term_Neq : constant W_Term_Id :=
            New_Operation
             (Name => Array_Access_Name.Id (Ada_Array),
              Parameters =>
               (1 => Index_Diff,
                2 => Upd_Term));
         Normal_Length : constant W_Term_Id :=
            --  'last - 'first + 1
            New_Arith_Operation
               (Left =>
                  New_Arith_Operation
                     (Left => Last_Term,
                      Op => New_Op_Substract,
                      Right => First_Term),
                Op => New_Op_Add,
                Right => New_Integer_Constant (Value => Uint_1));
         Enclosing : constant W_Predicate_Id :=
            New_Related_Terms
               (Left   => First_Term,
                Op     => New_Rel_Le,
                Right  => Index,
                Op2    => New_Rel_Le,
                Right2 => Last_Term);
      begin
         Emit
           (File,
            New_Parameter
              (Name    => To_Program_Space (Array_Access_Name.Id (Ada_Array)),
               Binders =>
                 (1 => Index_Binder,
                  2 => Ar_Binder),
               Return_Type => A,
               Pre => Enclosing,
               Post =>
                 New_Equal
                   (New_Result_Term,
                    New_Operation
                      (Name => Array_Access_Name.Id (Ada_Array),
                       Parameters =>
                         (1 => Index,
                          2 => Ar)))));
         Emit
           (File,
            New_Parameter
              (Name    => To_Program_Space (Array_Update_Name.Id (Ada_Array)),
               Binders =>
                 (1 => Index_Binder,
                  2 => Ar_Binder,
                  3 => Component_Binder),
               Return_Type => Ar_Type,
               Pre => Enclosing,
               Post =>
                 New_Equal
                    (New_Result_Term,
                     New_Operation
                        (Name => Array_Update_Name.Id (Ada_Array),
                         Parameters =>
                           (1 => Index,
                            2 => Ar,
                            3 => Component)))));

         Emit
           (File,
            New_Guarded_Axiom
              (Name =>
                 Array_Accupd_Eq_Axiom.Id (Ada_Array),
               Binders =>
                 (1 => Ar_Binder,
                  2 => Index_Binder),
               Def =>
                 New_Universal_Quantif
                   (Variables => (1 => New_Identifier ("v")),
                    Var_Type  => +A,
                    Triggers  =>
                      New_Triggers (
                        Triggers => (1 =>
                                       New_Trigger (
                                         Terms => (1 => Upd_Term)))),
                    Pred      =>
                      New_Equal
                        (Acc_Upd_Term_Eq,
                         Component))));
         Emit
           (File,
            New_Guarded_Axiom
              (Name =>
                 Array_Accupd_Neq_Axiom.Id (Ada_Array),
               Binders =>
                 (1 => Ar_Binder,
                  2 => Index_Binder,
                  3 => Index_Diff_Binder),
               Def =>
                 New_Universal_Quantif
                   (Variables => (1 => New_Identifier ("v")),
                    Var_Type  => +A,
                    Triggers  =>
                      New_Triggers
                        (Triggers =>
                          (1 => New_Trigger
                            (Terms => (1 => Acc_Upd_Term_Neq)),
                           2 => New_Trigger
                             (Terms => (1 => Upd_Term, 2 => Get_Term)))),
                   Pred      =>
                     New_Implication
                       (Left  =>
                          New_NEqual
                            (Index,
                             Index_Diff),
                        Right =>
                          New_Equal
                            (Acc_Upd_Term_Neq, Get_Term)))));
         Emit
           (File,
            New_Guarded_Axiom
              (Name =>
                 Array_First_Update.Id (Ada_Array),
               Binders =>
                 (1 => Ar_Binder,
                  2 => Index_Binder,
                  3 => Component_Binder),
               Def =>
                 New_Equal
                   (First_Term,
                    New_Operation
                      (Name => Array_First_Name.Id (Ada_Array),
                       Parameters =>
                         (1 => Upd_Term)))));
         Emit
           (File,
            New_Guarded_Axiom
              (Name =>
                 Array_Last_Update.Id (Ada_Array),
               Binders =>
                 (1 => Ar_Binder,
                  2 => Index_Binder,
                  3 => Component_Binder),
               Def =>
                 New_Equal
                   (Last_Term,
                    New_Operation
                      (Name => Array_Last_Name.Id (Ada_Array),
                       Parameters =>
                         (1 => Upd_Term)))));
         Emit
           (File,
            New_Guarded_Axiom
              (Name =>
                 Array_Length_Update.Id (Ada_Array),
               Binders =>
                 (1 => Ar_Binder,
                  2 => Index_Binder,
                  3 => Component_Binder),
               Def =>
                 New_Equal
                   (Length_Term,
                    New_Operation
                      (Name => Array_Length_Name.Id (Ada_Array),
                       Parameters => (1 => Upd_Term)))));
         Emit
           (File,
            New_Guarded_Axiom
              (Name =>
                 Array_Length_Non_Zero.Id (Ada_Array),
               Binders =>
                 (1 => Ar_Binder),
               Def =>
                 New_Implication
                   (Left  =>
                      New_Related_Terms
                        (Left  => Last_Term,
                         Right => First_Term,
                         Op    => New_Rel_Ge),
                    Right =>
                      New_Equal
                        (Left  => Length_Term,
                         Right => Normal_Length))));
         Emit
           (File,
            New_Guarded_Axiom
              (Name =>
                 Array_Length_Zero.Id (Ada_Array),
               Binders =>
                 (1 => Ar_Binder),
               Def =>
                 New_Implication
                   (Left  =>
                      New_Related_Terms
                        (Left  => Last_Term,
                         Right => First_Term,
                         Op    => New_Rel_Lt),
                    Right =>
                      New_Equal
                        (Left  => Length_Term,
                         Right =>
                           New_Integer_Constant (Value => Uint_0)))));
      end;
   end Declare_Generic_Array_Type;

   ---------------------------
   -- New_Array_Access_Prog --
   ---------------------------

   function New_Array_Access_Prog
     (Ada_Node      : Node_Id;
      Type_Name     : String;
      Ar            : W_Prog_Id;
      Index         : W_Prog_Id) return W_Prog_Id
   is
   begin
      return
         New_Located_Call
            (Ada_Node => Ada_Node,
             Reason   => VC_Array_Bounds_Check,
             Name     => To_Program_Space (Array_Access_Name.Id (Ada_Array)),
             Progs    =>
               (1 => Index,
                2 =>
                  New_Prog_Call
                     (Name  => Array_Conv_From.Id (Type_Name),
                      Progs => (1 => Ar))));
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
          (Name => Array_Access_Name.Id (Ada_Array),
           Parameters =>
            (1 => Index,
             2 =>
               New_Operation
                  (Name => Array_Conv_From.Id (Type_Name),
                   Parameters => (1 => Ar))));
   end New_Array_Access_Term;

   --------------------------
   -- New_Array_First_Prog --
   --------------------------

   function New_Array_First_Prog
     (Type_Name : String;
      Ar : W_Prog_Id) return W_Prog_Id is
   begin
      return
        New_Prog_Call
          (Name => Array_First_Name.Id (Ada_Array),
           Progs =>
            (1 =>
               New_Prog_Call
                  (Name => Array_Conv_From.Id (Type_Name),
                   Progs => (1 => Ar))));
   end New_Array_First_Prog;

   ---------------------------
   -- New_Array_First_Term --
   ---------------------------

   function New_Array_First_Term
     (Type_Name : String;
      Ar : W_Term_Id) return W_Term_Id is
   begin
      return
        New_Operation
          (Name => Array_First_Name.Id (Ada_Array),
           Parameters =>
            (1 =>
               New_Operation
                  (Name => Array_Conv_From.Id (Type_Name),
                   Parameters => (1 => Ar))));
   end New_Array_First_Term;

   --------------------------
   -- New_Array_Last_Prog --
   --------------------------

   function New_Array_Last_Prog
     (Type_Name : String;
      Ar : W_Prog_Id) return W_Prog_Id is
   begin
      return
        New_Prog_Call
          (Name => Array_Last_Name.Id (Ada_Array),
           Progs =>
            (1 =>
               New_Prog_Call
                  (Name => Array_Conv_From.Id (Type_Name),
                   Progs => (1 => Ar))));
   end New_Array_Last_Prog;

   -------------------------
   -- New_Array_Last_Term --
   -------------------------

   function New_Array_Last_Term
     (Type_Name : String;
      Ar : W_Term_Id) return W_Term_Id is
   begin
      return
        New_Operation
          (Name => Array_Last_Name.Id (Ada_Array),
           Parameters =>
            (1 =>
               New_Operation
                  (Name => Array_Conv_From.Id (Type_Name),
                   Parameters => (1 => Ar))));
   end New_Array_Last_Term;

   --------------------------
   -- New_Array_Length_Prog --
   --------------------------

   function New_Array_Length_Prog
     (Type_Name : String;
      Ar : W_Prog_Id) return W_Prog_Id is
   begin
      return
        New_Prog_Call
          (Name => Array_Length_Name.Id (Ada_Array),
           Progs =>
            (1 =>
               New_Prog_Call
                  (Name => Array_Conv_From.Id (Type_Name),
                   Progs => (1 => Ar))));
   end New_Array_Length_Prog;

   ---------------------------
   -- New_Array_Length_Term --
   ---------------------------

   function New_Array_Length_Term
     (Type_Name : String;
      Ar : W_Term_Id) return W_Term_Id is
   begin
      return
        New_Operation
          (Name => Array_Length_Name.Id (Ada_Array),
           Parameters =>
            (1 =>
               New_Operation
                  (Name => Array_Conv_From.Id (Type_Name),
                   Parameters => (1 => Ar))));
   end New_Array_Length_Term;

   ---------------------------
   -- New_Array_Update_Prog --
   ---------------------------

   function New_Array_Update_Prog
      (Ada_Node      : Node_Id;
       Type_Name     : String;
       Ar            : W_Identifier_Id;
       Index         : W_Prog_Id;
       Value         : W_Prog_Id) return W_Prog_Id
   is
   begin
      return
         New_Assignment
            (Name => Ar,
             Value =>
               New_Prog_Call
                 (Name => Array_Conv_To.Id (Type_Name),
                  Progs =>
                     (1 =>
                        New_Located_Call
                          (Ada_Node => Ada_Node,
                           Reason   => VC_Array_Bounds_Check,
                           Name     =>
                              To_Program_Space
                                (Array_Update_Name.Id (Ada_Array)),
                           Progs    =>
                              (1 => Index,
                               2 => New_Prog_Call
                                      (Name => Array_Conv_From.Id (Type_Name),
                                       Progs => (1 => New_Deref (Ref => Ar))),
                               3 => Value)))));
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
          (Name => Array_Conv_To.Id (Type_Name),
           Parameters =>
            (1 =>
               New_Operation
                 (Name => Array_Update_Name.Id (Ada_Array),
                  Parameters =>
                    (1 => Index,
                     2 =>
                        New_Operation
                           (Name => Array_Conv_From.Id (Type_Name),
                            Parameters => (1 => Ar)),
                     3 => Value))));
   end New_Array_Update_Term;

end Why.Gen.Arrays;
