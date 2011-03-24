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

with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Axioms;     use Why.Gen.Axioms;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Preds;      use Why.Gen.Preds;
with Why.Gen.Terms;      use Why.Gen.Terms;

package body Why.Gen.Arrays is

   function New_Binder (Arg, Arg_Type : String) return W_Binder_Id;
   --  Return a binder with the given argument name and argument type.

   function New_Binder (Arg : String; Arg_Type : W_Computation_Type_Id)
      return W_Binder_Id;
   --  Return a binder with the given argument name and argument type.

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
      function To_Int (T : W_Term_Id) return W_Term_Id;
      --  Convert a term of "index" type to an "int"

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
         Pre : constant W_Predicate_Id :=
            New_Related_Terms
               (Left   =>
                  To_Int
                    (New_Operation
                       (Name => Array_First_Name (Name),
                        Parameters => (1 => New_Term (Arg_A)))),
                Op     => New_Rel_Le,
                Right  =>
                  To_Int (New_Term (Arg_I)),
                Op2    => New_Rel_Le,
                Right2 =>
                  To_Int
                    (New_Operation
                      (Name => Array_Last_Name (Name),
                       Parameters => (1 => New_Term (Arg_A)))));
      begin
         declare
            --  Binders and postcondition for update
            Binders : constant W_Binder_Array :=
               (1 => New_Binder (Arg_I, Index),
                2 =>
                  New_Binder
                   (Arg_A,
                    New_Ref_Type
                        (Aliased_Type =>
                           New_Abstract_Type (Name => New_Identifier (Name)))),
                3 => New_Binder (Arg_V, Component));
            Post : constant W_Predicate_Id :=
               New_Equal
                  (Left => New_Term (Arg_A),
                   Right =>
                     New_Array_Update_Term
                        (Type_Name => Name,
                         Ar        => New_Old_Ident (New_Identifier (Arg_A)),
                         Index     => New_Term (Arg_I),
                         Value     => New_Term (Arg_V)));
         begin
            New_Parameter
               (File        => File,
                Name        => To_Program_Space (Array_Update_Name (Name)),
                Binders     => Binders,
                Return_Type => New_Type_Unit,
                Effects     =>
                  New_Effects (Writes => (1 => New_Identifier (Arg_A))),
                Pre         => New_Assertion (Pred => Pre),
                Post        => New_Assertion (Pred => Post));
         end;

         declare
            --  Binders and postcondition for access
            --  Binders and postcondition for update
            Binders : constant W_Binder_Array :=
               (1 => New_Binder (Arg_I, Index),
                2 => New_Binder (Arg_A, Name));
            Post : constant W_Predicate_Id :=
               New_Equal
                  (Left => New_Result_Identifier,
                   Right =>
                     New_Array_Access_Term
                        (Type_Name => Name,
                         Ar        => New_Old_Ident (New_Identifier (Arg_A)),
                         Index     => New_Term (Arg_I)));
         begin
            New_Parameter
               (File        => File,
                Name        => To_Program_Space (Array_Access_Name (Name)),
                Binders     => Binders,
                Return_Type =>
                  New_Abstract_Type (Name => New_Identifier (Component)),
                Pre         =>
                  New_Assertion (Pred => Duplicate_Any_Node (Id => Pre)),
                Post        => New_Assertion (Pred => Post));
         end;
      end;
   end Declare_Ada_Unconstrained_Array;

   ---------------------------
   -- New_Array_Access_Prog --
   ---------------------------

   function New_Array_Access_Prog
     (Type_Name     : String;
      Ar            : W_Prog_Id;
      Index         : W_Prog_Id;
      Unconstrained : Boolean) return W_Prog_Id
   is
      Name : constant W_Identifier_Id := Array_Access_Name (Type_Name);
   begin
      if Unconstrained then
         return
           New_Prog_Call
             (Name => To_Program_Space (Name),
              Progs => (1 => Index, 2 => Ar));
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
      (Type_Name     : String;
       Ar            : W_Identifier_Id;
       Index         : W_Prog_Id;
       Value         : W_Prog_Id;
       Unconstrained : Boolean) return W_Prog_Id
   is
      Name : constant W_Identifier_Id := Array_Update_Name (Type_Name);
   begin
      if Unconstrained then
         return
            New_Prog_Call
               (Name  => To_Program_Space (Name),
                Progs =>
                  (1 => Index,
                   2 => New_Prog_Identifier (Def => Ar),
                   3 => Value));
      else
         return
            New_Assignment
              (Name => Duplicate_Identifier (Id => Ar),
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

   function New_Binder (Arg : String; Arg_Type : W_Computation_Type_Id)
      return W_Binder_Id
   is
   begin
      return
         New_Binder
            (Names => (1 => New_Identifier (Arg)),
             Arg_Type => Arg_Type);
   end New_Binder;
end Why.Gen.Arrays;
