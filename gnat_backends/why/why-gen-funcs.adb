------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - F U N C S                         --
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

with Why.Sinfo;           use Why.Sinfo;
with Why.Atree.Mutators;  use Why.Atree.Mutators;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Tables;    use Why.Atree.Tables;

with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Arrows;      use Why.Gen.Arrows;

package body Why.Gen.Funcs is

   -----------------------
   -- Declare_Allocator --
   -----------------------

   procedure Declare_Allocator
     (File : W_File_Id;
      Name : String)
   is
      T_Id   : constant W_Identifier_Id := New_Identifier (Name);
      Arrows : constant W_Arrow_Type_Unchecked_Id :=
                 New_Arrow_Stack (New_Abstract_Type (Name => T_Id));
   begin
      Arrow_Type_Set_Left (Arrows, New_Type_Unit);
      Declare_Parameter (File,
                         Allocator_Name (Name),
                         Arrows,
                         Why_Empty,
                         New_True_Literal);
   end Declare_Allocator;

   -------------------
   -- Declare_Logic --
   -------------------

   procedure Declare_Logic
     (File   : W_File_Id;
      Name   : W_Identifier_Id;
      Arrows : W_Arrow_Type_Id)
   is
      Logic : constant W_Logic_Unchecked_Id := New_Unchecked_Logic;
      Spec  : constant W_Logic_Type_Unchecked_Id :=
                New_Unchecked_Logic_Type;

      procedure Append_To_Spec (Arrow : W_Arrow_Type_Id);
      --  Append the content of Arrow in the declaration of the
      --  logic function; in other words, build a logic spec from
      --  a program spec. e.g. transform:
      --
      --  x : type1 -> y : type2 -> {} type3 {}
      --
      --  ...into:
      --
      --  type1, type2 -> type3

      --------------------
      -- Append_To_Spec --
      --------------------

      procedure Append_To_Spec (Arrow : W_Arrow_Type_Id) is
         Right : constant W_Computation_Type_Id :=
                   Arrow_Type_Get_Right (Arrow);
      begin
         Logic_Type_Append_To_Arg_Types
           (Spec,
            Duplicate_Any_Node (Id => Arrow_Type_Get_Left (Arrow)));

         if Get_Kind (Right) = W_Computation_Spec then
            Logic_Type_Set_Return_Type
              (Spec,
               Duplicate_Any_Node
               (Id => Computation_Spec_Get_Return_Type (Right)));
         else
            Append_To_Spec (Right);
         end if;
      end Append_To_Spec;

   --  Start of processing for Declare_Logic

   begin
      Append_To_Spec (Arrows);
      Logic_Append_To_Names (Logic, Name);
      Logic_Set_Logic_Type (Logic, Spec);
      File_Append_To_Declarations (File,
                                   New_Logic_Declaration (Decl => Logic));
   end Declare_Logic;

   procedure Declare_Logic
     (File        : W_File_Id;
      Name        : W_Identifier_Id;
      Args        : Logic_Arg_Chain;
      Return_Type : W_Logic_Return_Type_Id)
   is
      Logic : constant W_Logic_Unchecked_Id := New_Unchecked_Logic;
      Spec  : constant W_Logic_Type_Unchecked_Id :=
                New_Unchecked_Logic_Type;
   begin
      for J in Args'Range loop
         Logic_Type_Append_To_Arg_Types (Spec, Args (J));
      end loop;

      Logic_Type_Set_Return_Type (Spec, Return_Type);
      Logic_Append_To_Names (Logic, Name);
      Logic_Set_Logic_Type (Logic, Spec);
      File_Append_To_Declarations (File,
                                   New_Logic_Declaration (Decl => Logic));
   end Declare_Logic;

   ----------------------------------
   -- Declare_Logic_And_Parameters --
   ----------------------------------

   procedure Declare_Logic_And_Parameters
     (File   : W_File_Id;
      Name   : W_Identifier_Id;
      Arrows : W_Arrow_Type_Id;
      Pre    : W_Predicate_OId := Why_Empty;
      Post   : W_Predicate_OId := Why_Empty)
   is
      Program_Space_Name : constant W_Identifier_Id :=
                             To_Program_Space (Name);
      Safe_Version_Name  : constant W_Identifier_Id :=
                             Safe_Version (Program_Space_Name);
      Safe_Arrows        : constant W_Arrow_Type_Id :=
                             Duplicate_Any_Node (Id => Arrows);
      Final_Post         : W_Predicate_OId := Post;
   begin
      Declare_Logic (File, Name, Arrows);

      if Final_Post = Why_Empty then
         declare
            Logic_Name : constant W_Identifier_Id :=
                           Duplicate_Any_Node (Id => Name);
         begin
            Final_Post := New_Related_Terms
              (Left  => New_Call_To_Logic (Logic_Name, Arrows),
               Op    => New_Rel_Eq,
               Right => New_Result_Identifier);
         end;
      end if;

      Declare_Parameter (File, Program_Space_Name, Arrows, Pre, Final_Post);
      Declare_Parameter (File,
                         Safe_Version_Name,
                         Safe_Arrows,
                         Why_Empty,
                         Duplicate_Any_Node (Id => Final_Post));
   end Declare_Logic_And_Parameters;

   -----------------------
   -- Declare_Parameter --
   -----------------------

   procedure Declare_Parameter
     (File   : W_File_Id;
      Name   : W_Identifier_Id;
      Arrows : W_Arrow_Type_Id;
      Pre    : W_Predicate_OId := Why_Empty;
      Post   : W_Predicate_OId := Why_Empty)
   is
      Parameter : constant W_Parameter_Declaration_Unchecked_Id :=
                    New_Unchecked_Parameter_Declaration;
   begin
      declare
         Contract : constant W_Computation_Spec_Id :=
                      Get_Computation_Spec (Arrows);
      begin
         if Pre /= Why_Empty then
            declare
               Assertion    : constant W_Assertion_Id :=
                                New_Assertion (Pred => Pre);
               Precondition : constant W_Postcondition_Id :=
                                New_Precondition (Assertion => Assertion);
            begin
               Computation_Spec_Set_Precondition
                 (Contract, Precondition);
            end;
         end if;

         if Post /= Why_Empty then
            declare
               Assertion     : constant W_Assertion_Id :=
                                 New_Assertion (Pred => Post);
               Postcondition : constant W_Postcondition_Id :=
                                 New_Postcondition (Assertion => Assertion);
            begin
               Computation_Spec_Set_Postcondition
                 (Contract, Postcondition);
            end;
         end if;
      end;

      Parameter_Declaration_Append_To_Names (Parameter, Name);
      Parameter_Declaration_Set_Parameter_Type (Parameter, Arrows);
      File_Append_To_Declarations (File, Parameter);
   end Declare_Parameter;

   -----------------------
   -- New_Call_To_Logic --
   -----------------------

   function New_Call_To_Logic
     (Name   : W_Identifier_Id;
      Arrows : W_Arrow_Type_Id)
     return W_Operation_Id
   is
      Operation : constant W_Operation_Unchecked_Id :=
                    New_Unchecked_Operation;

      procedure Append_Arg (Arrows : W_Arrow_Type_Id);
      --  Duplicate arg names from arrow and append them
      --  to Operation's arg lists.

      ----------------
      -- Append_Arg --
      ----------------

      procedure Append_Arg (Arrows : W_Arrow_Type_Id) is
         Right : constant W_Computation_Type_Id :=
                   Arrow_Type_Get_Right (Arrows);
      begin
         Operation_Append_To_Parameters
           (Operation,
            To_Term_Identifier (Arrow_Type_Get_Name (Arrows)));

         if Get_Kind (Right) /= W_Computation_Spec then
            Append_Arg (Right);
         end if;
      end Append_Arg;

   begin
      Operation_Set_Name (Operation, Name);
      Append_Arg (Arrows);
      return Operation;
   end New_Call_To_Logic;

   ----------------------------
   -- Declare_Global_Binding --
   ----------------------------

   procedure Declare_Global_Binding
      (File    : W_File_Id;
       Name    : String;
       Binders : W_Binder_Array;
       Pre     : W_Assertion_Id
                   := New_Assertion (Pred => New_True_Literal_Pred);
       Def     : W_Prog_Id;
       Post    : W_Assertion_Id
                   := New_Assertion (Pred => New_True_Literal_Pred))
   is
   begin
      File_Append_To_Declarations
         (File,
          New_Global_Binding
          (Name => New_Identifier (Name),
           Pre => New_Precondition (Assertion => Pre),
           Binders => Binders,
           Def =>
             New_Post_Assertion
               (Prog => Def,
                Post => New_Postcondition (Assertion => Post))));
   end Declare_Global_Binding;

end Why.Gen.Funcs;
