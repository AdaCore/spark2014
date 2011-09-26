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

with Why.Atree.Builders;        use Why.Atree.Builders;
with Why.Conversions;           use Why.Conversions;
with Why.Gen.Decl;              use Why.Gen.Decl;
with Why.Gen.Names;             use Why.Gen.Names;
with Why.Sinfo;                 use Why.Sinfo;

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
      R_Type      : constant W_Primitive_Type_Id :=
                 New_Abstract_Type (Name => New_Identifier (Name));
      W_Type      : constant W_Base_Type_Id := New_Base_Type (E, EW_Abstract);

      X_T         : constant W_Term_Id := +New_Identifier ("x");
      Y_T         : constant W_Term_Id := +New_Identifier ("y");
      Cmp_Binders : constant Binder_Array (1 .. 2) :=
                      (1 => (B_Name => New_Identifier ("x"),
                             B_Type => R_Type,
                             others => <>),
                       2 => (B_Name => New_Identifier ("y"),
                             B_Type => R_Type,
                             others => <>));

      Cond        : constant W_Pred_Id :=
                     New_Relation
                        (Left    => +X_T,
                         Right   => +Y_T,
                         Op_Type => EW_Bool,
                         Op      => EW_Eq);
      Def         : constant W_Term_Id :=
                     New_Conditional
                        (Condition   => W_Prog_Id (Cond),
                         Then_Part   => New_Literal (Value  => EW_True,
                                                     Domain => EW_Term),
                         Else_Part   => New_Literal (Value  => EW_False,
                                                     Domain => EW_Term));
   begin
      Emit (File,
        New_Record_Definition (Name    => New_Identifier (Name),
                               Binders => Binders));

      Emit
        (File,
         New_Function_Def
           (Domain      => EW_Term,
            Name        => New_Bool_Cmp (EW_Eq, W_Type),
            Binders     => Cmp_Binders,
            Return_Type => New_Base_Type (Base_Type => EW_Bool),
            Def         => +Def));
   end Define_Ada_Record;

end Why.Gen.Records;
