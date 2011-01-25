------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - T Y P E S                         --
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
with Einfo;              use Einfo;
with Namet;              use Namet;
with Nlists;             use Nlists;
with Sem_Eval;           use Sem_Eval;
with Sinfo;              use Sinfo;
with String_Utils;       use String_Utils;
with Uintp;              use Uintp;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Ints;       use Why.Gen.Ints;
with Why.Gen.Enums;      use Why.Gen.Enums;
with Why.Gen.Funcs;      use Why.Gen.Funcs;

package body Gnat2Why.Types is

   -------------------------------------
   -- Why_Type_Decl_of_Gnat_Type_Decl --
   -------------------------------------

   procedure Why_Type_Decl_of_Gnat_Type_Decl
      (File : W_File_Id;
       Node : Node_Id)
   is
      Name                : constant Name_Id :=
                              Chars (Defining_Identifier (Node));
      Name_Str            : constant String := Get_Name_String (Name);
   begin
      --  Types_Table.Insert (Name, Why_Type_Id);
      case Nkind (Node) is
         when N_Full_Type_Declaration =>
            declare
               Def_Node : constant Node_Id := Type_Definition (Node);
            begin
               case Nkind (Def_Node) is
               when N_Enumeration_Type_Definition =>
                  declare
                     Cursor       : Node_Or_Entity_Id :=
                                      Nlists.First (Literals (Def_Node));
                     Constructors : String_Lists.List :=
                                      String_Lists.Empty_List;
                  begin
                     while Nkind (Cursor) /= N_Empty loop
                        Constructors.Append (
                          Get_Name_String (Chars (Cursor)));
                        Cursor := Next (Cursor);
                     end loop;
                     Declare_Ada_Enum_Type (File, Name_Str, Constructors);
                  end;

               when N_Signed_Integer_Type_Definition =>
                  Declare_Ada_Abstract_Signed_Int
                    (File,
                     Name_Str,
                     Expr_Value (Low_Bound (Def_Node)),
                     Expr_Value (High_Bound (Def_Node)));
               when others => null;
               end case;
            end;
         when N_Subtype_Declaration =>
            case Nkind (Subtype_Indication (Node)) is
            when N_Identifier =>
               declare
                  Sc_Range   : constant Node_Id :=
                     Scalar_Range (Defining_Identifier (Node));
                  Base_Type : constant String :=
                     Get_Name_String (Chars (Subtype_Indication (Node)));
                  Low       : constant Uint :=
                     Expr_Value (Low_Bound (Sc_Range));
                  High       : constant Uint :=
                     Expr_Value (High_Bound (Sc_Range));

               begin
                  Declare_Ada_Abstract_Signed_Int (File, Name_Str, Low, High);
                  Declare_Ada_Range_Subtype_Relation
                    (File,
                     Name_Str,
                     Base_Type);
               end;
            when others => null;
            end case;
         --  ??? TBD Complete This code
         when others => raise Program_Error;
      end case;
   end Why_Type_Decl_of_Gnat_Type_Decl;

   -------------------------------
   -- Why_Prog_Type_of_Ada_Type --
   -------------------------------

   function Why_Prog_Type_of_Ada_Type
     (Ty : Node_Id) return W_Computation_Type_Id
   is
      Name : constant Name_Id := Chars (Etype (Ty));
   begin
      --  We have to use the full name of the type
      return
        New_Ref_Type
          (Ada_Node     => Ty,
           Aliased_Type => New_Abstract_Type
                             (Ada_Node => Ty,
                              Name => New_Identifier
                                        (Ada_Node => Ty,
                                         Symbol => Name)));
   end  Why_Prog_Type_of_Ada_Type;

end Gnat2Why.Types;
