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

with Why.Gen.Decl;        use Why.Gen.Decl;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Binders;     use Why.Gen.Binders;
with Why.Conversions;     use Why.Conversions;

package body Why.Gen.Preds is

   -------------------------
   -- Define_Eq_Predicate --
   -------------------------

   procedure Define_Eq_Predicate
     (Theory         : W_Theory_Declaration_Id;
      Why3_Type_Name : W_Identifier_Id;
      Base_Type      : EW_Scalar)
   is
      X_S               : constant W_Identifier_Id :=
        New_Identifier (Name => "x");
      Y_S               : constant W_Identifier_Id :=
        New_Identifier (Name => "y");
      X_Binder          : constant Binder_Type :=
                            (B_Name => X_S,
                             B_Type =>
                               New_Abstract_Type (Name => Why3_Type_Name),
                             others => <>);
      Y_Binder          : constant Binder_Type :=
                            (B_Name => Y_S,
                             B_Type =>
                               New_Abstract_Type (Name => Why3_Type_Name),
                             others => <>);

      --  <base_type>_of___<name> (x) = <base_type>_of___<name> (y)
      Conversion        : constant W_Identifier_Id :=
        To_Ident (Convert_To (Base_Type));
      X_To_Base_Type_Op : constant W_Term_Id :=
                            New_Call
                              (Name   => Conversion,
                               Args   => (1 => +X_S));
      Y_To_Base_Type_Op : constant W_Term_Id :=
                            New_Call
                              (Name   => Conversion,
                               Args   => (1 => +Y_S));
   begin
      --  ...now set the pieces together:
      Emit
        (Theory,
         New_Function_Def
           (Name    => To_Ident (WNE_Eq),
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
     (Theory    : W_Theory_Declaration_Id;
      Base_Type : EW_Scalar)
   is
      BT         : constant W_Primitive_Type_Id
                     := New_Base_Type (Base_Type => Base_Type);

      --  Identifiers
      Arg_S      : constant W_Identifier_Id := New_Identifier (Name => "x");

      --  predicate <name>___in_range (x : <base_type>) = [...]
      Pred_Name  : constant W_Identifier_Id := To_Ident (WNE_Range_Pred);
      Binder     : constant Binder_Type :=
                     (B_Name => Arg_S,
                      B_Type => BT,
                      others => <>);
      Decl       : constant W_Pred_Id :=
            +New_Relation
               (Op_Type => Base_Type,
                Left    => +To_Ident (WNE_Attr_First),
                Op      => EW_Le,
                Right   => +Arg_S,
                Op2     => EW_Le,
                Right2  => +To_Ident (WNE_Attr_Last));
   begin
      Emit
        (Theory,
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
