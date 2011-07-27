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

with Atree;                use Atree;
with Einfo;                use Einfo;
with Sem_Util;             use Sem_Util;
with Sinfo;                use Sinfo;
with Stand;                use Stand;

with Why.Atree.Builders;   use Why.Atree.Builders;
with Why.Conversions;      use Why.Conversions;
with Why.Gen.Decl;         use Why.Gen.Decl;
with Why.Gen.Names;        use Why.Gen.Names;
with Why.Gen.Preds;        use Why.Gen.Preds;
with Why.Inter;            use Why.Inter;

with Gnat2Why.Types;       use Gnat2Why.Types;
with Gnat2Why.Subprograms; use Gnat2Why.Subprograms;

package body Gnat2Why.Decls is

   function Is_Local_Lifted (N : Node_Id) return Boolean;
   --  Given an N_Defining_Identifier, decide if the variable is local or
   --  global

   ---------------
   -- Full_Name --
   ---------------

   function Full_Name (N : Node_Id) return String is
   begin
      if N = Standard_Boolean then
         return "bool";
      else
         return Unique_Name (N);
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
      Id  : Entity_Id;
      Def  : Node_Id := Empty)
   is
      Name   : constant String := Full_Name (Id);
   begin
      --  If the object is mutable, we generate a global ref
      if Is_Mutable (Id) then
         New_Global_Ref_Declaration
            (File     => File,
             Name     => New_Identifier (Name),
             Obj_Type => +Why_Logic_Type_Of_Ada_Obj (Id));

      else
         --  otherwise we can generate a "logic", with a defining axiom if
         --  necessary and possible.
         New_Logic
            (File        => File,
             Name        => New_Identifier (Name),
             Args        => (1 .. 0 => <>),
             Return_Type => +Why_Logic_Type_Of_Ada_Obj (Id));
         if Present (Def) and then Is_Static_Expression (Def) then
            declare
               Ax_Name : constant String := Name & "__def_axiom";
               Ident : constant W_Identifier_Id := New_Identifier (Name);
            begin
               New_Axiom
                  (File       => File,
                   Name       => New_Identifier (Ax_Name),
                   Axiom_Body =>
                     New_Equal
                        (Left  => New_Term_Identifier (Name => Ident),
                         Right => Why_Term_Of_Ada_Expr (Def,
                           Why_Abstract (Etype (Id)))));
            end;
         end if;
      end if;

   end Why_Decl_Of_Ada_Object_Decl;
end Gnat2Why.Decls;
