------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - R E C O R D S                       --
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

with Why.Atree.Tables;    use Why.Atree.Tables;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Mutators;  use Why.Atree.Mutators;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Gen.Decl;        use Why.Gen.Decl;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Axioms;      use Why.Gen.Axioms;

package body Why.Gen.Records is

   -------------------
   -- Add_Component --
   -------------------

   procedure Add_Component
     (File    : W_File_Id;
      C_Name  : String;
      C_Type  : W_Primitive_Type_Id;
      Builder : W_Logic_Type_Id)
   is
      R_Type : constant W_Primitive_Type_Id :=
                 +Logic_Type_Get_Return_Type (Builder);
   begin
      New_Logic
         (File        => File,
          Name        => Record_Getter_Name (C_Name),
          Args        => (1 => +Duplicate_Any_Node (Id => +R_Type)),
          Return_Type =>       +C_Type);
      Logic_Type_Append_To_Arg_Types
         (Builder,
          +Duplicate_Any_Node (Id => +C_Type));
   end Add_Component;

   -----------------------
   -- Freeze_Ada_Record --
   -----------------------

   procedure Freeze_Ada_Record
     (File    : W_File_Id;
      Name    : String;
      C_Names : String_Lists.List;
      Builder : W_Logic_Type_Id)
   is
      use String_Lists;

      C_Types : constant W_Logic_Arg_Type_OList :=
                  Logic_Type_Get_Arg_Types (Builder);
   begin
      if Is_Empty (+C_Types) then
         return;
      end if;

      --  Workaround for K526-008 and K525-019

      --  for C_Name of C_Names loop
      --   Define_Getter_Axiom
      --     (File,
      --      Name,
      --      C_Name,
      --      C_Names,
      --      Builder);
      --  end loop;

      declare
         C : Cursor := C_Names.First;
      begin
         while C /= No_Element loop
            Define_Getter_Axiom
              (File,
               Name,
               Element (C),
               C_Names,
               Builder);
            Next (C);
         end loop;
      end;
   end Freeze_Ada_Record;

   ----------------------------------
   -- Start_Ada_Record_Declaration --
   ----------------------------------

   procedure Start_Ada_Record_Declaration
     (File    : W_File_Id;
      Name    : String;
      Builder : out W_Logic_Type_Id)
   is
   begin
      New_Abstract_Type (File, Name);
      Builder :=
        New_Logic_Type (Return_Type =>
                          New_Abstract_Type (Name => New_Identifier (Name)));
      File_Append_To_Declarations
        (Id => File,
         New_Item => New_Logic_Declaration
         (Decl => New_Logic
          (Names => (1 => Record_Builder_Name (Name)),
           Logic_Type => Builder)));
   end Start_Ada_Record_Declaration;

end Why.Gen.Records;
