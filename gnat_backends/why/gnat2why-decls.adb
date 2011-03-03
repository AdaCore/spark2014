------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - D E C L S                            --
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

with Atree;                use Atree;
with Einfo;                use Einfo;
with Namet;                use Namet;
with Sinfo;                use Sinfo;
with Stand;                use Stand;
with Why.Atree.Builders;   use Why.Atree.Builders;
with Why.Gen.Decl;         use Why.Gen.Decl;
with Why.Gen.Names;        use Why.Gen.Names;
with Why.Gen.Preds;        use Why.Gen.Preds;

with Gnat2Why.Subprograms; use Gnat2Why.Subprograms;
with Gnat2Why.Types;       use Gnat2Why.Types;

package body Gnat2Why.Decls is

   ---------------
   -- Full_Name --
   ---------------

   function Full_Name (N : Node_Id) return String
   is
      Short_Name  : constant String  := Get_Name_String (Chars (N));
   begin
      if N = Standard_Boolean then
         return "bool";
      end if;
      --  We expand all names except parameters
      if Has_Fully_Qualified_Name (N) or else
         Ekind (N) in E_Out_Parameter ..  E_In_Parameter or else
         Ekind (N) = E_Loop_Parameter
      then
         return Short_Name;
      else
         return (Get_Name_String (Chars (Scope (N))) & "__" & Short_Name);
      end if;
   end Full_Name;

   ---------------------
   -- Is_Local_Lifted --
   ---------------------

   function Is_Local_Lifted (N : Node_Id) return Boolean
   is
   begin
      return
         (Ekind (Scope (N)) in Subprogram_Kind and then
          not (Ekind (N) in E_Out_Parameter .. E_In_Parameter));
   end Is_Local_Lifted;

   ----------------
   -- Is_Mutable --
   ----------------

   function Is_Mutable (N : Node_Id) return Boolean
   is
      Is_Constant : constant Boolean :=
         Ekind (N) = E_Constant or else Ekind (N) = E_In_Parameter;
   begin
      return (Is_Local_Lifted (N) or else not Is_Constant);
   end Is_Mutable;

   ---------------------------------
   -- Why_Decl_Of_Ada_Object_Decl --
   ---------------------------------

   procedure Why_Decl_Of_Ada_Object_Decl
     (File : W_File_Id;
      Decl : Node_Id)
   is
      --  For global object declarations we distinguish:
      --  * Really global variables: we can use the name of the
      --    variable as-is, also we can transform it into a logic +
      --    axiom if it is constant
      --  * Lifted local variables: we need to prefix the variable
      --    name with a scope, and we always translate to reference
      --    parameters
      Obj_Id : constant Node_Id := Defining_Identifier (Decl);
      Name   : constant String := Full_Name (Obj_Id);
   begin
      if Is_Mutable (Obj_Id) then
         New_Parameter
            (File        => File,
             Name        => New_Identifier (Name),
             Binders     => (1 .. 0 => <>),
             Return_Type => Why_Prog_Type_Of_Ada_Type (Obj_Id));
      else
         --  the case of a global constant

         New_Logic
            (File        => File,
             Name        => New_Identifier (Name),
             Args        => (1 .. 0 => <>),
             Return_Type => Why_Prog_Type_Of_Ada_Type (Obj_Id));
         if Present (Expression (Decl)) then
            declare
               Ax_Name : constant String := Name & "__def_axiom";
               Id : constant W_Identifier_Id := New_Identifier (Name);
            begin
               New_Axiom
                  (File       => File,
                   Name       => New_Identifier (Ax_Name),
                   Axiom_Body =>
                     New_Equal
                        (Left  => New_Term_Identifier (Name => Id),
                         Right => Why_Term_Of_Ada_Expr (Expression (Decl))));
            end;
         end if;
      end if;

   end Why_Decl_Of_Ada_Object_Decl;
end Gnat2Why.Decls;
