------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - D E C L                           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2015, AdaCore                   --
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

with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Modules;   use Why.Atree.Modules;
with Why.Atree.Mutators;  use Why.Atree.Mutators;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Sinfo;           use Why.Sinfo;
with Why.Types;           use Why.Types;

with Common_Containers;   use Common_Containers;

package body Why.Gen.Decl is

   ----------
   -- Emit --
   ----------

   procedure Emit
     (Theory : W_Theory_Declaration_Id;
      Decl : W_Declaration_Id) is
   begin
      Theory_Declaration_Append_To_Declarations
        (Id => Theory,
         New_Item => +Decl);
   end Emit;

   ---------------------------
   -- New_Havoc_Declaration --
   ---------------------------

   function New_Havoc_Declaration (Name : W_Name_Id) return W_Declaration_Id
   is
      Typ       : constant W_Type_Id := New_Type
        (Type_Kind  => EW_Abstract,
         Name       => Ref_Append (Name));
      Havoc_Fun : constant W_Identifier_Id :=
        Havoc_Append (Name);
      X         : constant W_Identifier_Id :=
        New_Identifier (Domain => EW_Prog,
                        Name   => "x",
                        Typ    => Typ);
   begin
      return New_Function_Decl
                 (Domain      => EW_Prog,
                  Name        => Havoc_Fun,
                  Binders     => (1 => New_Binder (Domain   => EW_Prog,
                                                   Name     => X,
                                                   Arg_Type => Typ)),
                  Effects     => New_Effects (Writes   => (1 => X)),
                  Return_Type => EW_Unit_Type,
                  Labels      => Name_Id_Sets.Empty_Set);
   end New_Havoc_Declaration;

   -----------------------------
   -- New_Ref_Type_Definition --
   -----------------------------

   function New_Ref_Type_Definition (Name : W_Name_Id) return W_Declaration_Id
   is
      Typ : constant W_Type_Id := New_Type
        (Type_Kind  => EW_Abstract,
         Name       => Name);
   begin
      return Why.Atree.Builders.New_Type_Decl
        (Name       => Ref_Append (Name),
         Labels     => Name_Id_Sets.Empty_Set,
         Definition => New_Record_Definition
           (Fields   =>
              (1 => New_Record_Binder
                   (Domain     => EW_Term,
                    Name       =>
                      Content_Append (Name, Typ),
                    Arg_Type   => Typ,
                    Is_Mutable => True))));
   end New_Ref_Type_Definition;

   -------------------
   -- New_Type_Decl --
   -------------------

   function New_Type_Decl (Name : String) return W_Declaration_Id is
   begin
      return
        New_Type_Decl
          (Name   => New_Name (Symbol => NID (Name)),
           Labels => Name_Id_Sets.Empty_Set);
   end New_Type_Decl;

   function New_Type_Decl
     (Name  : W_Name_Id;
      Alias : W_Type_Id) return W_Declaration_Id is
   begin
      return New_Type_Decl
        (Name => Name,
         Labels => Name_Id_Sets.Empty_Set,
         Definition => New_Transparent_Type_Definition
           (Domain          => EW_Prog,
            Type_Definition => Alias));
   end New_Type_Decl;

end Why.Gen.Decl;
