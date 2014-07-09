------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - T Y P E S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2014, AdaCore                   --
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

--  For debugging, to print info on the output before raising an exception
with Ada.Text_IO;
use Ada.Text_IO;

with GNAT.Source_Info;

with Atree;               use Atree;
with Einfo;               use Einfo;
with Namet;               use Namet;
with Sinfo;               use Sinfo;
with Sinput;              use Sinput;
with Stand;               use Stand;

with SPARK_Definition;    use SPARK_Definition;
with SPARK_Util;          use SPARK_Util;

with Why;                 use Why;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Modules;   use Why.Atree.Modules;
with Why.Conversions;     use Why.Conversions;
with Why.Gen.Arrays;      use Why.Gen.Arrays;
with Why.Gen.Binders;     use Why.Gen.Binders;
with Why.Gen.Decl;        use Why.Gen.Decl;
with Why.Gen.Expr;        use Why.Gen.Expr;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Records;     use Why.Gen.Records;
with Why.Gen.Scalars;     use Why.Gen.Scalars;
with Why.Inter;           use Why.Inter;
with Why.Sinfo;           use Why.Sinfo;
with Why.Types;           use Why.Types;

with Gnat2Why.Nodes;      use Gnat2Why.Nodes;

package body Gnat2Why.Types is

   ------------------------------
   -- Generate_Type_Completion --
   ------------------------------

   procedure Generate_Type_Completion
     (File       : in out Why_Section;
      E          : Entity_Id)
   is
      Eq   : Entity_Id := Has_User_Defined_Eq (E);
      Ty   : constant W_Type_Id := EW_Abstract (E);
   begin
      Open_Theory
        (File, E_Axiom_Module (E),
         Comment =>
           "Module giving axioms for the type entity "
         & """" & Get_Name_String (Chars (E)) & """"
         & (if Sloc (E) > 0 then
              " defined at " & Build_Location_String (Sloc (E))
           else "")
         & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  This module only contains an axiom when there is a user-provided
      --  equality

      if Present (Eq)
        and then Entity_In_SPARK (Eq)
      then

         --  we may need to adjust for renamed subprograms

         if Present (Renamed_Entity (Eq)) then
            Eq := Renamed_Entity (Eq);
         end if;

         declare
            Need_Convert : constant Boolean :=
              Is_Scalar_Type (E) and then not Is_Boolean_Type (E);
            Var_A : constant W_Identifier_Id :=
              New_Identifier (Ada_Node => E,
                              Name     => "a",
                              Typ      => Ty);
            Var_B : constant W_Identifier_Id :=
              New_Identifier (Ada_Node => E,
                              Name     => "b",
                              Typ      => Ty);
            Arg_A : constant W_Expr_Id :=
              (if Need_Convert then
                  Insert_Simple_Conversion
                 (Domain => EW_Term,
                  Expr   => +Var_A,
                  To     => Base_Why_Type (Ty))
               else +Var_A);
            Arg_B : constant W_Expr_Id :=
              (if Need_Convert then
                  Insert_Simple_Conversion
                 (Domain => EW_Term,
                  Expr   => +Var_B,
                  To     => Base_Why_Type (Ty))
               else +Var_B);
            Def   : constant W_Expr_Id :=
              New_Call
                (Ada_Node => Eq,
                 Domain   => EW_Pred,
                 Name     => To_Why_Id (E => Eq,
                                        Domain => EW_Pred,
                                        Typ => EW_Bool_Type),
                 Args     => (1 => Arg_A, 2 => Arg_B),
                 Typ      => EW_Bool_Type);
         begin
            Emit
              (File.Cur_Theory,
               New_Defining_Axiom
                 (Ada_Node    => E,
                  Binders     =>
                    (1 => Binder_Type'(B_Name => Var_A, others => <>),
                     2 => Binder_Type'(B_Name => Var_B, others => <>)),
                  Name        =>
                    New_Identifier
                      (Module => E_Module (E),
                       Name    => "user_eq"),
                  Return_Type => EW_Bool,
                  Def         => +Def));
         end;
      end if;
      Close_Theory (File,
                    Kind => Axiom_Theory,
                    Defined_Entity => E);
   end Generate_Type_Completion;

   -----------------------
   -- Ident_Of_Ada_Type --
   -----------------------

   function Ident_Of_Ada_Type (E : Entity_Id) return W_Name_Id
   is
   begin
      if Is_Standard_Boolean_Type (E) then
         return Get_Name (EW_Bool_Type);
      elsif Fullview_Not_In_SPARK (E) then
         return Get_Name (EW_Private_Type);
      else
         return To_Why_Type (E);
      end if;
   end Ident_Of_Ada_Type;

   --------------------
   -- Translate_Type --
   --------------------

   procedure Translate_Type
     (File       : in out Why_Section;
      E          : Entity_Id;
      New_Theory : out Boolean)
   is
      procedure Translate_Underlying_Type
        (Theory : W_Theory_Declaration_Id;
         E      : Entity_Id);
      --  Translate a non-private type entity E

      -------------------------------
      -- Translate_Underlying_Type --
      -------------------------------

      procedure Translate_Underlying_Type
        (Theory : W_Theory_Declaration_Id;
         E      : Entity_Id) is

      begin
         case Ekind (E) is
            when Scalar_Kind =>
               Declare_Scalar_Type (Theory, E);

            when Array_Kind =>
               Declare_Ada_Array (Theory, E);

            when E_Record_Type | E_Record_Subtype =>
               Declare_Ada_Record (File, Theory, E);

            when Private_Kind =>
               Declare_Private_Type (Theory, E);

            when others =>
               Ada.Text_IO.Put_Line ("[Translate_Underlying_Type] ekind ="
                                     & Entity_Kind'Image (Ekind (E)));
               raise Not_Implemented;
         end case;
      end Translate_Underlying_Type;

      --  Start of Translate_Type

   begin
      if Is_Standard_Boolean_Type (E) or else E = Universal_Fixed then
         New_Theory := False;
         return;

      else
         New_Theory := True;

         Open_Theory
           (File, E_Module (E),
            Comment =>
              "Module for axiomatizing type "
            & """" & Get_Name_String (Chars (E)) & """"
            & (if Sloc (E) > 0 then
                 " defined at " & Build_Location_String (Sloc (E))
              else "")
            & ", created in " & GNAT.Source_Info.Enclosing_Entity);

         Translate_Underlying_Type (File.Cur_Theory, E);

         --  We declare a default value for all types, in principle.
         --  Cloned subtypes are a special case, they do not need such a
         --  definition.

         if Is_Record_Type (E) and then
           (if Ekind (E) = E_Record_Subtype then
                not (Present (Cloned_Subtype (E))))
         then
            Emit
              (File.Cur_Theory,
               Why.Atree.Builders.New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => To_Ident (WNE_Dummy),
                  Binders     => (1 .. 0 => <>),
                  Labels      => Name_Id_Sets.Empty_Set,
                  Return_Type =>
                    +New_Named_Type (Name => To_Why_Type (E, Local => True))));
         end if;

         --  If E is the full view of a private type, use its partial view as
         --  the filtering entity, as it is the entity used everywhere in AST.

         if Is_Full_View (E) then
            Close_Theory (File,
                          Kind => Definition_Theory,
                          Defined_Entity => Partial_View (E));
         else
            Close_Theory (File,
                          Kind => Definition_Theory,
                          Defined_Entity => E);
         end if;
      end if;
   end Translate_Type;

end Gnat2Why.Types;
