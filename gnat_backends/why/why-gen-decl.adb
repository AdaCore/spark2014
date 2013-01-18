------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - D E C L                           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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
with Why.Atree.Mutators;  use Why.Atree.Mutators;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Sinfo;           use Why.Sinfo;

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

   --------------
   -- New_Type --
   --------------

   function New_Type (Name : String) return W_Declaration_Id is
   begin
      return New_Type (Name => New_Identifier (Name => Name));
   end New_Type;

   function New_Type
     (Name  : W_Identifier_Id;
      Alias : W_Primitive_Type_Id) return W_Declaration_Id is
   begin
      return New_Type
        (Name => Name,
         Definition => New_Transparent_Type_Definition
           (Domain          => EW_Prog,
            Type_Definition => Alias));
   end New_Type;

   function New_Type
     (Name : W_Identifier_Id;
      Args : Natural)
     return W_Declaration_Id
   is
      C       : Character := 'a';
      Type_Ar : W_Identifier_Array := (1 .. Args => <>);
   begin
      if Args = 0 then
         return New_Type (Name => Name);
      end if;

      for I in 1 .. Args loop
         Type_Ar (I) := New_Identifier (Name => (1 => C));
         C := Character'Succ (C);
      end loop;

      return
        New_Type
          (Name => Name,
           Args => Type_Ar);
   end New_Type;

   ------------------------
   -- New_Adt_Definition --
   ------------------------

   function New_Adt_Definition
     (Name         : W_Identifier_Id;
      Constructors : W_Constr_Decl_Array)
     return W_Declaration_Id is
   begin
      return
        New_Type
          (Name => Name,
           Definition =>
             New_Adt_Definition (Constructors => Constructors));
   end New_Adt_Definition;

end Why.Gen.Decl;
