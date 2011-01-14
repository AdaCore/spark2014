------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - S U B P R O G R A M S                --
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

with Atree;              use Atree;
with Namet;              use Namet;
with Sinfo;              use Sinfo;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Atree.Mutators; use Why.Atree.Mutators;

package body Gnat2Why.Subprograms is
   procedure Why_Decl_of_Ada_Subprogram
      (File : W_File_Id;
       Node : Node_Id)
   is
      --  ??? This function has to be expanded to deal with Statements
      Is_Proc : Boolean := False;
      Spec    : constant Node_Id := Specification (Node);
--        Stmts : constant List_Id
--           := Statements (Handled_Statement_Sequence (Node));
      Name    : Name_Id;
   begin
      case Nkind (Spec) is
         when N_Procedure_Specification =>
            Is_Proc := True;
            Name := Chars (Defining_Unit_Name (Spec));
         when others => raise Program_Error;
      end case;
      if Is_Proc then
         File_Append_To_Declarations
            (File,
             New_Global_Binding
                (Node,
                 Name => New_Identifier (Symbol => Name),
                 Pre => New_Precondition
                          (Assertion => New_Assertion
                              (Pred => New_True_Literal_Pred)),
                 Def =>
                 New_Post_Assertion
                     (Prog => New_Prog_Constant (Def => New_Void_Literal),
                      Post => New_Postcondition
                        (Assertion => New_Assertion
                           (Pred => New_True_Literal_Pred)))));
      end if;
   end Why_Decl_of_Ada_Subprogram;
end Gnat2Why.Subprograms;
