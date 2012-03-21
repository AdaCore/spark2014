------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - D E C L S                            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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

with Alfa.Definition;      use Alfa.Definition;

with Why.Ids;              use Why.Ids;
with Why.Sinfo;            use Why.Sinfo;
with Why.Atree.Accessors;  use Why.Atree.Accessors;
with Why.Atree.Builders;   use Why.Atree.Builders;
with Why.Gen.Decl;         use Why.Gen.Decl;
with Why.Gen.Names;        use Why.Gen.Names;
with Why.Gen.Binders;      use Why.Gen.Binders;
with Why.Types;            use Why.Types;

with Gnat2Why.Expr;        use Gnat2Why.Expr;
with Gnat2Why.Types;       use Gnat2Why.Types;

package body Gnat2Why.Decls is

   -----------------------------
   -- Get_Expression_Function --
   -----------------------------

   function Get_Expression_Function (E : Entity_Id) return Node_Id is
      Decl_N : constant Node_Id := Parent (Get_Subprogram_Spec (E));
      Body_N : constant Node_Id := Get_Subprogram_Body (E);
      Orig_N : Node_Id;
   begin
      --  Get the original node either from the declaration for E, or from the
      --  subprogram body for E, which may be different if E is attached to a
      --  subprogram declaration.

      if Present (Original_Node (Decl_N)) then
         Orig_N := Original_Node (Decl_N);
      else
         Orig_N := Original_Node (Body_N);
      end if;

      if Nkind (Orig_N) = N_Expression_Function then
         return Orig_N;
      else
         return Empty;
      end if;
   end Get_Expression_Function;

   -------------------------
   -- Get_Subprogram_Body --
   -------------------------

   function Get_Subprogram_Body (E : Entity_Id) return Node_Id is
      Body_E : Entity_Id;
      N      : Node_Id;

   begin
      --  Retrieve the declaration for E

      N := Parent (Get_Subprogram_Spec (E));

      --  If this declaration is not a subprogram body, then it must be a
      --  subprogram declaration, from which we can retrieve the entity
      --  for the corresponding subprogram body.

      if Nkind (N) = N_Subprogram_Body then
         Body_E := E;
      else
         Body_E := Corresponding_Body (N);
      end if;

      --  Retrieve the subprogram body

      return Parent (Get_Subprogram_Spec (Body_E));
   end Get_Subprogram_Body;

   -------------------------
   -- Get_Subprogram_Spec --
   -------------------------

   function Get_Subprogram_Spec (E : Entity_Id) return Node_Id is
      N : Node_Id;

   begin
      N := Parent (E);

      if Nkind (N) = N_Defining_Program_Unit_Name then
         N := Parent (N);
      end if;

      return N;
   end Get_Subprogram_Spec;

   ----------------
   -- Is_Mutable --
   ----------------

   function Is_Mutable (N : Node_Id) return Boolean
   is
   begin

      --  A variable is translated as mutable in Why if it is not constant on
      --  the Ada side, or if it is a loop parameter (of an actual loop, not a
      --  quantified expression.

      if Ekind (N) = E_Loop_Parameter then
         if Present (Parent (N)) and then
            Nkind (Parent (N)) = N_Loop_Parameter_Specification and then
            Present (Parent (Parent (N))) and then
            Nkind (Parent (Parent (N))) = N_Iteration_Scheme and then
            Present (Parent (Parent (Parent (N)))) and then
            Nkind (Parent (Parent (Parent (N)))) = N_Quantified_Expression
         then
            return False;
         else
            return True;
         end if;
      elsif Ekind (N) = E_Enumeration_Literal or else
        Is_Constant_Object (N) or else
        Ekind (N) in Named_Kind then
         return False;
      else
         return True;
      end if;
   end Is_Mutable;

   ------------------------
   -- Translate_Variable --
   ------------------------

   procedure Translate_Variable
     (File : in out Why_File;
      E     : Entity_Id)
   is
      Name : constant String := Full_Name (E);
      Decl : constant W_Declaration_Id :=
        (if Object_Is_In_Alfa (E) then
            New_Type
              (Name  => To_Ident (WNE_Type),
               Alias => +Why_Logic_Type_Of_Ada_Obj (E))
         else
            New_Type
              (Name => To_Ident (WNE_Type),
               Args => 0));
      Typ  : constant W_Primitive_Type_Id :=
               New_Abstract_Type (Name => Get_Name (W_Type_Id (Decl)));

   begin
      Open_Theory (File, Name);

      --  Generate an alias for the name of the object's type, based on the
      --  name of the object. This is useful when generating logic functions
      --  from Ada functions, to generate additional parameters for the global
      --  objects read.

      Emit (File.Cur_Theory, Decl);

      --  We generate a global ref

      Emit
        (File.Cur_Theory,
         New_Global_Ref_Declaration
           (Name     => To_Why_Id (E, Local => True),
            Ref_Type => Typ));

      Close_Theory (File, Filter_Entity => E);
   end Translate_Variable;

   ------------------------
   -- Translate_Constant --
   ------------------------

   procedure Translate_Constant
     (File   : in out Why_File;
      E      : Entity_Id)
   is
      Base_Name : constant String := Full_Name (E);
      Name      : constant String :=
                    (if Is_Full_View (E) then
                       Base_Name & "__full_view"
                     else
                       Base_Name);
      Typ  : constant W_Primitive_Type_Id := Why_Logic_Type_Of_Ada_Obj (E);
      Decl : constant Node_Id := Parent (E);
      Def  : W_Term_Id;

   begin
      --  Start with opening the theory to define, as the creation of a
      --  function for the logic term needs the current theory to insert an
      --  include declaration.

      Open_Theory (File, Name);

      --  Default values of parameters are not considered as the value of the
      --  constant representing the parameter.

      if Ekind (E) /= E_In_Parameter
        and then Present (Expression (Decl))
      then
         Def := Get_Pure_Logic_Term_If_Possible
           (File, Expression (Decl), Type_Of_Node (E));
      else
         Def := Why_Empty;
      end if;

      --  The definition of deferred constants is done in a separate theory, so
      --  that only code in the unit defining the deferred constant has access
      --  to its value. This allows supporting parameterized verification of
      --  client units not depending on the value of a delayed constant. This
      --  theory is added as a completion of the base theory defining the
      --  constant, so that further modules including the base theory also
      --  include the completion, for modules defined in this unit. Theories
      --  defined in other units only have access to the base theory. Note
      --  that modules in the same unit may also have access to the base
      --  theory only, if they are defined before this point.

      if Is_Full_View (E) then
         if Def = Why_Empty then
            Discard_Theory (File);

         else
            Emit
              (File.Cur_Theory,
               New_Defining_Axiom
                 (Name        => To_Why_Id (E, Local => False),
                  Return_Type => Get_EW_Type (Typ),
                  Binders     => (1 .. 0 => <>),
                  Def         => Def));
            Close_Theory (File, Filter_Entity => Empty);
            Add_Completion (Base_Name, Name);
         end if;

      --  In the general case, we generate a "logic", with a defining axiom if
      --  necessary and possible.

      else
         Emit
           (File.Cur_Theory,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => To_Why_Id (E, Local => True),
               Binders     => (1 .. 0 => <>),
               Return_Type => Typ));

         if Def /= Why_Empty then
            Emit
              (File.Cur_Theory,
               New_Defining_Axiom
                 (Name        => To_Why_Id (E, Local => True),
                  Return_Type => Get_EW_Type (Typ),
                  Binders     => (1 .. 0 => <>),
                  Def         => Def));
         end if;

         Close_Theory (File, Filter_Entity => E);
      end if;
   end Translate_Constant;

end Gnat2Why.Decls;
