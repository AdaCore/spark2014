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

with Atree;         use Atree;
with Namet;         use Namet;
with Nlists;        use Nlists;
with Sem_Eval;      use Sem_Eval;
with Sinfo;         use Sinfo;
with Why.Gen.Ints;  use Why.Gen.Ints;
with Why.Gen.Enums; use Why.Gen.Enums;
with Why.Gen.Types; use Why.Gen.Types;

package body Gnat2Why.Types is

   procedure Why_Type_Decl_of_Gnat_Type_Decl
      (File : W_File_Id;
         Node : Node_Id)
   is
      Name                : constant Name_Id :=
                              Chars (Defining_Identifier (Node));
      Name_Str            : constant String := Get_Name_String (Name);
      Def_Node            : Node_Id;
   begin
      --  Types_Table.Insert (Name, Why_Type_Id);
      case Nkind (Node) is
         when N_Full_Type_Declaration =>
            Def_Node := Type_Definition (Node);
            case Nkind (Def_Node) is
               when N_Enumeration_Type_Definition =>
                  declare
                     Cursor : Node_Or_Entity_Id :=
                        Nlists.First (Literals (Def_Node));
                     Constructors : String_Lists.List
                        := String_Lists.Empty_List;
                  begin
                     while Nkind (Cursor) /= N_Empty loop
                        Constructors.Append (
                           Get_Name_String (Chars (Cursor)));
                        Cursor := Next (Cursor);
                     end loop;
                     Declare_Enum_Type (File, Name_Str, Constructors);
                  end;
               when N_Signed_Integer_Type_Definition =>
                  Declare_Abstract_Signed_Int (
                     File,
                     Name_Str,
                     Expr_Value (Low_Bound (Def_Node)),
                     Expr_Value (High_Bound (Def_Node)));
               when others => null;
            end case;
         when N_Subtype_Declaration =>
            --  ??? TODO Complete This code
            null;
         when others => raise Program_Error;
      end case;
   end Why_Type_Decl_of_Gnat_Type_Decl;
end Gnat2Why.Types;
