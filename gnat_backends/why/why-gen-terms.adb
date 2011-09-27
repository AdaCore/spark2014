------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - G E N - T E R M S                    --
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

with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Tables;    use Why.Atree.Tables;
with Why.Conversions;     use Why.Conversions;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Progs;       use Why.Gen.Progs;
with Why.Inter;           use Why.Inter;
with Why.Sinfo;           use Why.Sinfo;

package body Why.Gen.Terms is

   ----------------------------
   -- Insert_Conversion_Term --
   ----------------------------

   function Insert_Conversion_Term
      (Ada_Node : Node_Id := Empty;
       To       : W_Base_Type_Id;
       From     : W_Base_Type_Id;
       Why_Term : W_Term_Id) return W_Term_Id
   is
      Base : constant W_Base_Type_Id := LCA (To, From);

      function Insert_Single_Conversion
        (To       : W_Base_Type_Id;
         From     : W_Base_Type_Id;
         Why_Term : W_Term_Id) return W_Term_Id;
      --  Assuming that there is at most one step between To and From in the
      --  type hierarchy (i.e. that it exists a conversion from From
      --  to To; a counterexample would be two abstract types whose base
      --  types differ), insert the corresponding conversion.

      function Insert_Single_Conversion
        (To       : W_Base_Type_Id;
         From     : W_Base_Type_Id;
         Why_Term : W_Term_Id) return W_Term_Id is
      begin
         if Eq (From, To) then
            return Why_Term;
         else
            return
              New_Call
                (Ada_Node => Ada_Node,
                 Name     => Conversion_Name (From => From, To => To),
                 Args     => (1 => +Why_Term));
         end if;
      end Insert_Single_Conversion;

   begin
      if Eq (To, From) then
         return Why_Term;
      end if;

      declare
         Up_From : constant W_Base_Type_Id := Up (From, Base);
         Up_To   : constant W_Base_Type_Id := Up (To, Base);
      begin
         return
           Insert_Single_Conversion
             (To   => To,
              From => Up_To,
              Why_Term =>
                Insert_Conversion_Term
                  (Ada_Node => Ada_Node,
                   To       => Up_To,
                   From     => Up_From,
                   Why_Term =>
                     Insert_Single_Conversion
                       (To   => Up_From,
                        From => From,
                        Why_Term => Why_Term)));
      end;
   end Insert_Conversion_Term;

   -------------
   -- New_Ifb --
   -------------

   function New_Ifb (Condition, Left, Right : W_Term_Id) return W_Term_Id
   is
   begin
      case Get_Kind (+Condition) is
         when W_Literal =>
            if Get_Value (+Condition) = EW_True then
               return Left;
            else
               return Right;
            end if;

         when others =>
            return
              New_Call
                (Name => New_Identifier ("ite"),
                 Args => (1 => +Condition, 2 => +Left, 3 => +Right));
      end case;
   end New_Ifb;

   ---------------------
   -- New_Result_Term --
   ---------------------

   function New_Result_Term return W_Term_Id
   is
   begin
      return +New_Result_Identifier.Id;
   end New_Result_Term;

   ----------------------------
   -- New_Simpl_Epsilon_Term --
   ----------------------------

   function New_Simpl_Epsilon_Term
     (T : W_Primitive_Type_Id) return W_Term_Id is
   begin
      return
        New_Epsilon
          (Binder =>
               New_Binder (Domain   => EW_Term,
                           Name     => New_Identifier ("x"),
                           Arg_Type => +T),
           Pred   => New_Literal (Value => EW_True));
   end New_Simpl_Epsilon_Term;

   function New_Simpl_Epsilon_Term
     (T    : W_Primitive_Type_Id;
      Id   : W_Identifier_Id;
      Pred : W_Pred_Id) return W_Term_Id is
   begin
      return
        New_Epsilon
          (Binder =>
               New_Binder (Domain   => EW_Term,
                           Name     => Id,
                           Arg_Type => +T),
           Pred   => Pred);
   end New_Simpl_Epsilon_Term;

end Why.Gen.Terms;
