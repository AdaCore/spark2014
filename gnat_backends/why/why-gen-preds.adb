------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - P R E D S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
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
with Why.Atree.Mutators; use Why.Atree.Mutators;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Consts;     use Why.Gen.Consts;

package body Why.Gen.Preds is

   ----------------------------
   -- Define_Range_Predicate --
   ----------------------------

   procedure Define_Range_Predicate
     (File  : W_File_Id;
      Name  : String;
      First : Uint;
      Last  : Uint)
   is
      --  Identifiers
      Arg_S      : constant String := "x";
      First_S    : constant String := "first";
      Last_S     : constant String := "last";

      --  predicate <name>___in_range (x : int) = [...]
      Pred_Name  : constant W_Identifier_Id := Range_Pred_Name (Name);
      Binder     : constant W_Binder_Id :=
                     New_Logic_Binder (Name       => New_Identifier (Arg_S),
                                       Param_Type => New_Type_Int);

      --  let first = <first> in
      --  let last  = <last>  in [...]
      Decl_First : constant W_Binding_Pred_Unchecked_Id :=
                     New_Binding_Pred (First_S, First);
      Decl_Last  : constant W_Binding_Pred_Unchecked_Id :=
                     New_Binding_Pred (Last_S, Last);

      --  first <= x <= last
      Context    : constant W_Predicate_Id :=
                     New_Related_Terms (Left   => New_Term (First_S),
                                        Op     => New_Rel_Le,
                                        Right  => New_Term (Arg_S),
                                        Op2    => New_Rel_Le,
                                        Right2 => New_Term (Last_S));
      Pred_Body  : constant W_Predicate_Id :=
                     New_Predicate_Body ((Decl_First, Decl_Last), Context);
      Result     : constant W_Predicate_Definition_Unchecked_Id :=
                     New_Unchecked_Predicate_Definition;
   begin
      --  ...now set the pieces together:
      Predicate_Definition_Set_Name (Result, Pred_Name);
      Predicate_Definition_Append_To_Binders (Result, Binder);
      Predicate_Definition_Set_Def (Result, Pred_Body);
      File_Append_To_Declarations (File,
                                   New_Logic_Declaration (Decl => Result));
   end Define_Range_Predicate;

   ----------------------
   -- New_Binding_Pred --
   ----------------------

   function New_Binding_Pred
     (Name  : String;
      Value : Uint)
     return W_Binding_Pred_Unchecked_Id
   is
      Result : constant W_Binding_Pred_Unchecked_Id :=
                 New_Unchecked_Binding_Pred;
   begin
      Binding_Pred_Set_Name (Result, New_Identifier (Name));
      Binding_Pred_Set_Def (Result, New_Constant (Value));
      return Result;
   end New_Binding_Pred;

   ------------------------
   -- New_Predicate_Body --
   ------------------------

   function New_Predicate_Body
     (Bindings : Binding_Pred_Chain;
      Context  : W_Predicate_Id)
     return W_Predicate_Id is
   begin
      for J in reverse Bindings'Range loop
         if J = Bindings'Last then
            Binding_Pred_Set_Context (Bindings (J), Context);
         else
            Binding_Pred_Set_Context (Bindings (J), Bindings (J + 1));
         end if;
      end loop;

      return Bindings (Bindings'First);
   end New_Predicate_Body;

end Why.Gen.Preds;
