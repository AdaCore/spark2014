------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - P R E D S                         --
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

with Snames;              use Snames;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Gen.Decl;        use Why.Gen.Decl;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Binders;     use Why.Gen.Binders;
with Why.Conversions;     use Why.Conversions;

package body Why.Gen.Preds is

   -------------------------
   -- Define_Eq_Predicate --
   -------------------------

   procedure Define_Eq_Predicate
     (File      : W_File_Id;
      Name      : String;
      Base_Type : EW_Scalar)
   is
      Base_Type_Name    : constant String := EW_Base_Type_Name (Base_Type);

      --  Identifiers
      X_S               : constant String := "x";
      Y_S               : constant String := "y";

      --  predicate eq___<name> (x : <name>, y : <name>) = [...]
      Pred_Name         : constant W_Identifier_Id := Eq_Pred_Name.Id (Name);
      X_Binder          : constant Binder_Type :=
                            (B_Name => New_Identifier (X_S),
                             B_Type => New_Abstract_Type
                                         (Name => New_Identifier (EW_Term,
                                                                  Name)),
                             others => <>);
      Y_Binder          : constant Binder_Type :=
                            (B_Name => New_Identifier (Y_S),
                             B_Type => New_Abstract_Type
                                         (Name => New_Identifier (EW_Term,
                                                                  Name)),
                             others => <>);

      --  <base_type>_of___<name> (x) = <base_type>_of___<name> (y)
      Conversion        : constant W_Identifier_Id :=
                            Conversion_To.Id (Name, Base_Type_Name);
      X_To_Base_Type_Op : constant W_Term_Id :=
                            New_Call
                              (Name   => Conversion,
                               Args   => (1 => +New_Term (X_S)));
      Y_To_Base_Type_Op : constant W_Term_Id :=
                            New_Call
                              (Name   => Conversion,
                               Args   => (1 => +New_Term (Y_S)));
   begin
      --  ...now set the pieces together:
      Emit
        (File,
         New_Function_Def
           (Name    => Pred_Name,
            Domain  => EW_Pred,
            Binders => (1 => X_Binder, 2 => Y_Binder),
            Def     =>
              New_Relation
                (Domain  => EW_Pred,
                 Op      => EW_Eq,
                 Op_Type => Base_Type,
                 Left    => +X_To_Base_Type_Op,
                 Right   => +Y_To_Base_Type_Op)));
   end Define_Eq_Predicate;

   ----------------------------
   -- Define_Range_Predicate --
   ----------------------------

   procedure Define_Range_Predicate
     (File      : W_File_Id;
      Name      : String;
      Base_Type : EW_Scalar)
   is
      BT         : constant W_Primitive_Type_Id
                     := New_Base_Type (Base_Type => Base_Type);

      --  Identifiers
      Arg_S      : constant String := "x";

      --  predicate <name>___in_range (x : <base_type>) = [...]
      Pred_Name  : constant W_Identifier_Id := Range_Pred_Name.Id (Name);
      Binder     : constant Binder_Type :=
                     (B_Name => New_Identifier (Arg_S),
                      B_Type => BT,
                      others => <>);
      Decl       : constant W_Pred_Id :=
            +New_Relation
               (Op_Type => Base_Type,
                Left    =>
                    +Attr_Name.Id
                      (Name,
                       Attribute_Id'Image (Attribute_First)),
                Op      => EW_Le,
                Right   => +New_Term (Arg_S),
                Op2     => EW_Le,
                Right2  =>
                    +Attr_Name.Id
                      (Name,
                       Attribute_Id'Image (Attribute_Last)));
   begin
      Emit
        (File,
         New_Function_Def
           (Domain  => EW_Pred,
            Name    => Pred_Name,
            Binders => (1 => Binder),
            Def     => +Decl));
   end Define_Range_Predicate;

   --------------------
   -- New_Equal_Bool --
   --------------------

   function New_Equal_Bool
     (Left  : W_Term_Id;
      Right : W_Pred_Id) return W_Pred_Id
   is
   begin
      return
        New_Connection
          (Op    => EW_Equivalent,
           Left  =>
             New_Relation
               (Domain  => EW_Prog,
                Op      => EW_Eq,
                Op_Type => EW_Bool,
                Left    => +Left,
                Right   => New_Literal (Value => EW_True, Domain => EW_Prog)),
           Right => +Right);
   end New_Equal_Bool;

end Why.Gen.Preds;
