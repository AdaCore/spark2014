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
with Sinfo;                use Sinfo;

with Why.Types;            use Why.Types;
with Why.Sinfo;            use Why.Sinfo;
with Why.Inter;            use Why.Inter;
with Why.Atree.Builders;   use Why.Atree.Builders;
with Why.Conversions;      use Why.Conversions;
with Why.Gen.Decl;         use Why.Gen.Decl;
with Why.Gen.Names;        use Why.Gen.Names;
with Why.Gen.Binders;      use Why.Gen.Binders;
with Gnat2Why.Types;       use Gnat2Why.Types;
with Gnat2Why.Expr;        use Gnat2Why.Expr;

package body Gnat2Why.Decls is

   ----------------
   -- Is_Mutable --
   ----------------

   function Is_Mutable (N : Node_Id) return Boolean
   is
   begin

      --  A variable is translated as mutable in Why if it is not constant on
      --  the Ada side, or if it is a loop parameter.

      if Ekind (N) = E_Loop_Parameter then
         return True;
      elsif Is_Constant_Object (N) then
         return False;
      elsif Ekind (N) in Named_Kind then
         return False;
      else
         return True;
      end if;
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

      function Term_Definition return W_Term_Id;
      --  If possible, return a term equivalent to Def. Otherwise,
      --  return Why_Empty.

      ---------------------
      -- Term_Definition --
      ---------------------

      function Term_Definition return W_Term_Id is
      begin
         if Present (Def) and then Is_Static_Expression (Def) then
            return +Transform_Expr (Def, Type_Of_Node (Id), EW_Term);
         else
            return Why_Empty;
         end if;
      end Term_Definition;

   begin
      --  If the object is mutable, we generate a global ref

      if Is_Mutable (Id) then
         Emit
           (File,
            New_Global_Ref_Declaration
              (Name     => New_Identifier (Name),
               Ref_Type => +Why_Logic_Type_Of_Ada_Obj (Id)));

      --  Otherwise we can generate a "logic", with a defining axiom if
      --  necessary and possible.

      else
         Emit_Top_Level_Declarations
           (File        => File,
            Name        => New_Identifier (Name),
            Binders     => (1 .. 0 => <>),
            Return_Type => Why_Logic_Type_Of_Ada_Obj (Id),
            Spec        =>
              (1 =>
                 (Kind   => W_Function_Decl,
                  Domain => EW_Term,
                  Def    => Term_Definition,
                  others => <>)));
      end if;
   end Why_Decl_Of_Ada_Object_Decl;

end Gnat2Why.Decls;
