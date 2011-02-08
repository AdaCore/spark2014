------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - P R O G S                         --
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

with Uintp;              use Uintp;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Names;      use Why.Gen.Names;

package body Why.Gen.Progs is

   ---------------------
   -- Conversion_Name --
   ---------------------

   function Conversion_Name
      (From : Why_Type;
       To   : Why_Type) return W_Identifier_Id
   is
   begin
      case From.Kind is
         when Why_Int =>
            case To.Kind is
               when Why_Int =>
                  --  We have assumed the two arguments to be different
                  raise Program_Error;
               when Why_Abstract =>
                  return
                     New_Conversion_From_Int
                       (Get_Name_String (To.Wh_Abstract));
            end case;
         when Why_Abstract =>
            case To.Kind is
               when Why_Int =>
                  return
                    New_Conversion_To_Int (Get_Name_String (From.Wh_Abstract));
               when Why_Abstract =>
                  raise Program_Error
                     with "Conversion between arbitrary types attempted";
            end case;
      end case;
   end Conversion_Name;

   -----------------------
   -- Insert_Conversion --
   -----------------------

   function Insert_Conversion
      (Ada_Node : Node_Id := Empty;
       To       : Why_Type;
       From     : Why_Type;
       Why_Expr : W_Prog_Id) return W_Prog_Id
   is
   begin
      if To = From then
         return Why_Expr;
      end if;

      if To.Kind = Why_Int or else From.Kind = Why_Int then
         return
           New_Prog_Call
             (Ada_Node => Ada_Node,
              Name     => Conversion_Name (From => From, To => To),
              Progs    => (1 => Why_Expr));
      else
         return
            Insert_Conversion
               (Ada_Node => Ada_Node,
                To       => To,
                From     => (Kind => Why_Int),
                Why_Expr =>
                  Insert_Conversion
                    (Ada_Node => Ada_Node,
                     To       => (Kind => Why_Int),
                     From     => From,
                     Why_Expr => Why_Expr));
      end if;
   end Insert_Conversion;

   ------------------
   -- New_For_Loop --
   ------------------

   function New_For_Loop
     (Ada_Node   : Node_Id;
      Loop_Index : Name_Id;
      Index_Type : Why_Type;
      Low        : W_Prog_Id;
      High       : W_Prog_Id;
      Invariant  : W_Loop_Annot_Id;
      Loop_Body  : W_Prog_Id) return W_Prog_Id
   is
      Index_Deref : constant W_Prog_Id :=
         New_Deref
           (Ada_Node => Ada_Node,
            Ref      => New_Identifier (Symbol => Loop_Index));
      Int_Of_Index : constant W_Prog_Id :=
        Insert_Conversion
           (Ada_Node => Ada_Node,
            To       => (Kind => Why_Int),
            From     => Index_Type,
            Why_Expr => Index_Deref);
      Addition : constant W_Prog_Id :=
         New_Infix_Call
            (Ada_Node => Ada_Node,
             Infix    => New_Op_Add_Prog,
             Left     => Int_Of_Index,
             Right    =>
               New_Prog_Constant
                 (Ada_Node => Ada_Node,
                  Def      =>
                    New_Integer_Constant
                      (Ada_Node => Ada_Node,
                      Value     => Uint_1)));
      Incr_Stmt : constant W_Prog_Id :=
         New_Assignment
            (Ada_Node => Ada_Node,
             Name     =>
               New_Identifier (Symbol => Loop_Index),
             Value    =>
               Insert_Conversion
                  (Ada_Node => Ada_Node,
                   To       => Index_Type,
                   From     => (Kind => Why_Int),
                   Why_Expr => Addition));
      In_Range_Expression : constant W_Prog_Id  :=
         New_Infix_Call
           (Ada_Node => Ada_Node,
            Infix    => New_Op_And_Then_Prog,
            Left     =>
               New_Infix_Call
                 (Ada_Node => Ada_Node,
                  Infix    => New_Op_Le_Prog,
                  Left     => Low,
                  Right    =>
                    Duplicate_Any_Node (Id => Int_Of_Index)),
            Right    =>
               New_Infix_Call
                 (Ada_Node => Ada_Node,
                  Infix    => New_Op_Le_Prog,
                  Left     =>
                    Duplicate_Any_Node (Id => Int_Of_Index),
                  Right    => High));
      Loop_Content : constant W_Prog_Id :=
         New_Statement_Sequence
            (Ada_Node   => Ada_Node,
             Statements => (1 => Loop_Body, 2 => Incr_Stmt));
   begin
      return
        New_Binding_Ref
           (Ada_Node => Ada_Node,
            Name     => New_Identifier (Symbol => Loop_Index),
            Def      =>
               Insert_Conversion
                  (Ada_Node => Ada_Node,
                   From     => (Kind => Why_Int),
                   To       => Index_Type,
                   Why_Expr => Duplicate_Any_Node (Id => Low)),
            Context  =>
              New_While_Loop
                (Ada_Node     => Ada_Node,
                 Condition    => In_Range_Expression,
                 Annotation   => Invariant,
                 Loop_Content => Loop_Content));
   end New_For_Loop;

end Why.Gen.Progs;
