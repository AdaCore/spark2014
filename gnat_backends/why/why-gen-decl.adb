------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - D E C L                           --
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

with Why.Conversions;     use Why.Conversions;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Mutators;  use Why.Atree.Mutators;
with Why.Atree.Tables;    use Why.Atree.Tables;
with Why.Gen.Names;       use Why.Gen.Names;

package body Why.Gen.Decl is

   -----------------------
   -- New_Abstract_Type --
   -----------------------

   procedure New_Abstract_Type (File : W_File_Id; Name : String)
   is
   begin
      File_Append_To_Declarations
        (+File,
         New_Logic_Declaration
           (Decl => New_Type (Name => New_Identifier (Name))));
   end New_Abstract_Type;

   procedure New_Abstract_Type (File : W_File_Id; Name : W_Identifier_Id)
   is
   begin
      File_Append_To_Declarations
        (+File,
         New_Logic_Declaration
           (Decl => New_Type (Name => Name)));
   end New_Abstract_Type;

   ------------------------
   -- New_Adt_Definition --
   ------------------------

   procedure New_Adt_Definition
     (File : W_File_Id;
      Name : W_Identifier_Id;
      Constructors : W_Constr_Decl_Array)
   is
   begin
      File_Append_To_Declarations
         (+File,
          New_Logic_Declaration
            (Decl =>
               New_Type
                 (Name => Name,
                  Definition =>
                     New_Adt_Definition (Constructors => Constructors))));
   end New_Adt_Definition;

   ---------------
   -- New_Axiom --
   ---------------

   procedure New_Axiom
      (File       : W_File_Id;
       Name       : W_Identifier_Id;
       Axiom_Body : W_Predicate_Id)
   is
   begin
      File_Append_To_Declarations
        (+File,
         New_Logic_Declaration
            (Decl => New_Axiom (Name => Name, Def => Axiom_Body)));
   end New_Axiom;

   -------------------
   -- New_Exception --
   -------------------

   procedure New_Exception
      (File      : W_File_Id;
       Name      : W_Identifier_Id;
       Parameter : W_Primitive_Type_Id)
   is
   begin
      File_Append_To_Declarations
         (+File,
          New_Exception_Declaration (Name => Name, Parameter => Parameter));
   end New_Exception;

   ------------------------
   -- New_Global_Binding --
   ------------------------

   procedure New_Global_Binding
      (File    : W_File_Id;
       Name    : W_Identifier_Id;
       Binders : W_Binder_Array;
       Pre     : W_Assertion_Id
                   := New_Assertion (Pred => New_True_Literal_Pred);
       Def     : W_Prog_Id;
       Post    : W_Assertion_Id
                   := New_Assertion (Pred => New_True_Literal_Pred))
   is
   begin
      File_Append_To_Declarations
         (+File,
          New_Global_Binding
          (Name => Name,
           Pre => New_Precondition (Assertion => Pre),
           Binders => Binders,
           Def =>
             New_Post_Assertion
               (Prog => Def,
                Post => New_Postcondition (Assertion => Post))));
   end New_Global_Binding;

   -----------------------------
   -- New_Include_Declaration --
   -----------------------------

   procedure New_Include_Declaration
     (File : W_File_Id;
      Name : W_Identifier_Id;
      Ada_Node : Node_Id := Empty)
   is
   begin
      File_Append_To_Declarations
        (Id => +File,
         New_Item =>
           New_Include_Declaration
             (Ada_Node => Ada_Node,
              Name     => Name));
   end New_Include_Declaration;

   ---------------
   -- New_Logic --
   ---------------

   procedure New_Logic
     (File        : W_File_Id;
      Name        : W_Identifier_Id;
      Args        : W_Logic_Arg_Type_Array;
      Return_Type : W_Logic_Return_Type_Id)
   is
   begin
      File_Append_To_Declarations
        (Id => +File,
         New_Item =>
           New_Logic_Declaration (Decl =>
              New_Logic
                (Names => (1 => Name),
                 Logic_Type =>
                   New_Logic_Type
                     (Arg_Types   => Args,
                      Return_Type => Return_Type))));
   end New_Logic;

   -------------------
   -- New_Parameter --
   -------------------

   procedure New_Parameter
      (File        : W_File_Id;
       Name        : W_Identifier_Id;
       Binders     : W_Binder_Array;
       Return_Type : W_Value_Type_Id;
       Effects     : W_Effects_Id := New_Effects;
       Pre         : W_Assertion_Id
           := New_Assertion (Pred => New_True_Literal_Pred);
       Post        : W_Assertion_Id
           := New_Assertion (Pred => New_True_Literal_Pred))
   is
      Param_Type : W_Computation_Type_Id;
   begin
      if Binders'Length = 0 then
         Param_Type := +Return_Type;
      else
         Param_Type :=
            New_Computation_Spec
              (Return_Type   => Return_Type,
               Effects       => Effects,
               Precondition  => New_Precondition (Assertion => Pre),
               Postcondition => New_Postcondition (Assertion => Post));
         for Index in reverse Binders'Range loop
            declare
               use Node_Lists;

               Cur_Binder : constant W_Binder_Id := Binders (Index);
               Arg_Ty     : constant W_Value_Type_Id :=
                  Binder_Get_Arg_Type (Cur_Binder);
               Names      : constant Node_Lists.List :=
                  Get_List (+Binder_Get_Names (Cur_Binder));
               Cur        : Node_Lists.Cursor := First (Names);
            begin
               while Has_Element (Cur) loop
                  Param_Type :=
                     New_Arrow_Type
                        (Name  => +Duplicate_Any_Node (Id => Element (Cur)),
                         Left  => +Duplicate_Any_Node (Id => +Arg_Ty),
                         Right => Param_Type);
                  Node_Lists.Next (Cur);
               end loop;
            end;
         end loop;
      end if;
      File_Append_To_Declarations
        (Id       => +File,
         New_Item =>
           New_Parameter_Declaration
            (Names => (1 => Name),
             Parameter_Type => +Param_Type));
   end New_Parameter;

   procedure New_Parameter
      (File       : W_File_Id;
       Name       : W_Identifier_Id;
       Value_Type : W_Value_Type_Id)
   is
   begin
      File_Append_To_Declarations
        (Id => +File,
         New_Item =>
            New_Parameter_Declaration
              (Names => (1 => Name),
               Parameter_Type => Value_Type));
   end New_Parameter;

   ------------------------------
   -- New_Predicate_Definition --
   ------------------------------

   procedure New_Predicate_Definition
     (File     : W_File_Id;
      Name     : W_Identifier_Id;
      Binders  : W_Logic_Binder_Array;
      Def      : W_Predicate_Id)
   is
   begin
      File_Append_To_Declarations
        (Id => +File,
         New_Item =>
           New_Logic_Declaration
             (Decl =>
               New_Predicate_Definition
                 (Name    => Name,
                  Binders => Binders,
                  Def     => Def)));
   end New_Predicate_Definition;

end Why.Gen.Decl;
