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

with Why.Sinfo;           use Why.Sinfo;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Gen.Decl;        use Why.Gen.Decl;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Axioms;      use Why.Gen.Axioms;

package body Why.Gen.Records is

   -----------------------
   -- Define_Ada_Record --
   -----------------------

   procedure Define_Ada_Record
     (File    : W_File_Id;
      E       : Entity_Id;
      Name    : String;
      Binders : Binder_Array)
   is
      R_Type : constant W_Primitive_Type_Id :=
                 New_Abstract_Type (Name => New_Identifier (Name));
      W_Type : constant W_Base_Type_Id := New_Base_Type (E, EW_Abstract);

      Cmp_Binders : constant Binder_Array (1 .. 2) :=
                      (1 => (B_Name => New_Identifier ("x"),
                             B_Type => R_Type,
                             others => <>),
                       2 => (B_Name => New_Identifier ("y"),
                             B_Type => R_Type,
                             others => <>));

   begin
      Emit (File, New_Type (Name));

      for J in Binders'Range loop
         Emit
           (File,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => Record_Getter_Name.Id (Binders (J).B_Name),
               Binders     => New_Binders ((1 => R_Type)),
               Return_Type => Binders (J).B_Type));
      end loop;

      Emit
        (File,
         New_Function_Decl
           (Domain      => EW_Term,
            Name        => Record_Builder_Name.Id (Name),
            Binders     => Binders,
            Return_Type => R_Type));

      for J in Binders'Range loop
         Define_Getter_Axiom
           (File,
            Name,
            J,
            Binders);
      end loop;

      Emit
        (File,
         New_Function_Decl
           (Domain      => EW_Term,
            Name        => New_Bool_Cmp (EW_Eq, W_Type),
            Binders     => Cmp_Binders,
            Return_Type => New_Base_Type (Base_Type => EW_Bool)));

      Define_Equality_Axiom
        (File,
         New_Identifier (Name),
         Binders);

   end Define_Ada_Record;

end Why.Gen.Records;
