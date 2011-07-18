------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - B I N D E R S                       --
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

with Why.Conversions; use Why.Conversions;
with Why.Gen.Names;   use Why.Gen.Names;
with Why.Gen.Decl;    use Why.Gen.Decl;
with Why.Gen.Terms;   use Why.Gen.Terms;

package body Why.Gen.Binders is

   function New_Computation_Type
     (Ada_Node    : Node_Id := Empty;
      Binders     : Binder_Array;
      Return_Type : W_Primitive_Type_Id;
      Effects     : W_Effects_Id := New_Effects;
      Pre         : W_Predicate_Id := New_True_Literal_Pred;
      Post        : W_Predicate_Id := New_True_Literal_Pred)
     return W_Computation_Type_Id;

   function New_Binders (Binders : Binder_Array) return W_Binder_Array;

   function New_Binders (Binders : Binder_Array) return W_Logic_Binder_Array;

   function New_Binders (Binders : Binder_Array) return W_Logic_Arg_Type_Array;

   function New_Term_Array (Binders : Binder_Array) return W_Term_Array;

   ---------------------------------
   -- Emit_Top_Level_Declarations --
   ---------------------------------

   procedure Emit_Top_Level_Declarations
     (File        : W_File_Id;
      Ada_Node    : Node_Id := Empty;
      Name        : W_Identifier_Id;
      Binders     : Binder_Array;
      Return_Type : W_Primitive_Type_Id;
      Spec        : in out Declaration_Spec_Array)
   is
      Logic_Def_Emitted : Boolean := False;
   begin
      for S in Spec'Range loop
         case Spec (S).Kind is
            when W_Logic =>
               pragma Assert (not Logic_Def_Emitted);
               if Spec (S).Name = Why_Empty then
                  Spec (S).Name := Logic_Func_Name (Name);
               end if;

               Emit
                 (File,
                  New_Logic
                    (Ada_Node    => Ada_Node,
                     Name        => Spec (S).Name,
                     Binders     => Binders,
                     Return_Type => Return_Type));
               Logic_Def_Emitted := True;

            when W_Function =>
               pragma Assert (not Logic_Def_Emitted);
               if Spec (S).Name = Why_Empty then
                  Spec (S).Name := Logic_Func_Name (Name);
               end if;

               Emit
                 (File,
                  New_Function
                    (Ada_Node    => Ada_Node,
                     Name        => Spec (S).Name,
                     Binders     => Binders,
                     Return_Type => Return_Type,
                     Def         => Spec (S).Term));
               Logic_Def_Emitted := True;

            when W_Predicate_Definition =>
               if Spec (S).Name = Why_Empty then
                  Spec (S).Name := Logic_Func_Name (Name);
               end if;

               Emit
                 (File,
                  New_Predicate_Definition
                    (Ada_Node    => Ada_Node,
                     Name        => Spec (S).Name,
                     Binders     => Binders,
                     Def         => Spec (S).Pred));

            when W_Global_Binding =>
               if Spec (S).Name = Why_Empty then
                  Spec (S).Name := New_Definition_Name (Name);
               end if;

               if Spec (S).Pre = Why_Empty then
                  Spec (S).Pre := New_True_Literal_Pred;
               end if;

               if Spec (S).Post = Why_Empty then
                  Spec (S).Post := New_True_Literal_Pred;
               end if;

               Emit
                 (File,
                  New_Global_Binding
                    (Ada_Node    => Ada_Node,
                     Name        => Spec (S).Name,
                     Binders     => Binders,
                     Pre         => Spec (S).Pre,
                     Def         => Spec (S).Prog,
                     Post        => Spec (S).Post));

            when W_Parameter_Declaration =>
               if Spec (S).Name = Why_Empty then
                  Spec (S).Name := Program_Func_Name (Name);
               end if;

               if Spec (S).Pre = Why_Empty then
                  Spec (S).Pre := New_True_Literal_Pred;
               end if;

               if Spec (S).Post = Why_Empty then
                  if Logic_Def_Emitted then
                     Spec (S).Post := New_Related_Terms
                       (Left  => New_Call_To_Logic
                                   (Name => Spec (S).Name,
                                    Binders => Binders),
                        Op    => New_Rel_Eq,
                        Right => New_Result_Term);
                  else
                     Spec (S).Post := New_True_Literal_Pred;
                  end if;
               end if;

               Emit
                 (File,
                  New_Parameter
                    (Ada_Node    => Ada_Node,
                     Name        => Spec (S).Name,
                     Binders     => Binders,
                     Return_Type => Return_Type,
                     Pre         => Spec (S).Pre,
                     Effects     => Spec (S).Effects,
                     Post        => Spec (S).Post));

            when others =>
               --  Invalid
               pragma Assert (False);
               null;
         end case;
      end loop;
   end Emit_Top_Level_Declarations;

   -----------------
   -- New_Binders --
   -----------------

   function New_Binders (Binders : Binder_Array) return W_Binder_Array is

      function New_Arg_Type
        (Binder : Binder_Type)
        return W_Simple_Value_Type_Id;

      ------------------
      -- New_Arg_Type --
      ------------------

      function New_Arg_Type
        (Binder : Binder_Type)
        return W_Simple_Value_Type_Id is
      begin
         case Binder.Modifier is
            when Array_Modifier =>
               return New_Array_Type (Component_Type => Binder.B_Type);
            when Ref_Modifier =>
               return New_Ref_Type (Aliased_Type => Binder.B_Type);
            when None =>
               return +Binder.B_Type;
         end case;
      end New_Arg_Type;

      Result : W_Binder_Array (Binders'Range);

   --  Start of processing for New_Binders

   begin
      for B in Binders'Range loop
         Result (B) := New_Binder
                         (Ada_Node => Binders (B).Ada_Node,
                          Names    => (1 => Binders (B).B_Name),
                          Arg_Type => New_Arg_Type (Binders (B)));
      end loop;

      return Result;
   end New_Binders;

   function New_Binders (Binders : Binder_Array) return W_Logic_Binder_Array is
      Result : W_Logic_Binder_Array (Binders'Range);
   begin
      for B in Binders'Range loop
         Result (B) :=
           New_Logic_Binder
             (Ada_Node   => Binders (B).Ada_Node,
              Name       => Binders (B).B_Name,
              Param_Type => Binders (B).B_Type);
      end loop;

      return Result;
   end New_Binders;

   function New_Binders
     (Binders : Binder_Array)
     return W_Logic_Arg_Type_Array
   is
      Result : W_Logic_Arg_Type_Array (Binders'Range);
   begin
      for B in Binders'Range loop
         Result (B) := +Binders (B).B_Type;
      end loop;

      return Result;
   end New_Binders;

   -----------------------
   -- New_Call_To_Logic --
   -----------------------

   function New_Call_To_Logic
     (Ada_Node : Node_Id := Empty;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array)
     return W_Term_Id is
   begin
      return New_Operation
        (Ada_Node   => Ada_Node,
         Name       => Name,
         Parameters => New_Term_Array (Binders));
   end New_Call_To_Logic;

   --------------------------
   -- New_Computation_Type --
   --------------------------

   function New_Computation_Type
     (Ada_Node    : Node_Id := Empty;
      Binders     : Binder_Array;
      Return_Type : W_Primitive_Type_Id;
      Effects     : W_Effects_Id := New_Effects;
      Pre         : W_Predicate_Id := New_True_Literal_Pred;
      Post        : W_Predicate_Id := New_True_Literal_Pred)
     return W_Computation_Type_Id is
   begin
      return New_Computation_Type
        (Ada_Node      => Ada_Node,
         Binders       => New_Binders (Binders),
         Precondition  => Pre,
         Effects       => Effects,
         Postcondition => New_Postcondition (Pred => Post),
         Return_Type   => Return_Type);
   end New_Computation_Type;

   -----------------------------
   -- New_Existential_Quantif --
   -----------------------------

   function New_Existential_Quantif
     (Ada_Node : Node_Id := Empty;
      Binders  : Binder_Array;
      Pred     : W_Predicate_Id)
     return W_Predicate_Id is
   begin
      if Binders'Length = 0 then
         return Pred;
      else
         return New_Existential_Quantif
           (Ada_Node  => Ada_Node,
            Variables => (1 => Binders (Binders'First).B_Name),
            Var_Type  => Binders (Binders'First).B_Type,
            Pred      =>
              New_Existential_Quantif (Empty,
                                       Binders (Binders'First + 1
                                                .. Binders'Last),
                                       Pred));
      end if;
   end New_Existential_Quantif;

   ------------------
   -- New_Function --
   ------------------

   function New_Function
     (Ada_Node    : Node_Id := Empty;
      Name        : W_Identifier_Id;
      Binders     : Binder_Array;
      Return_Type : W_Primitive_Type_Id;
      Def         : W_Term_Id)
     return W_Logic_Declaration_Class_Id is
   begin
      return New_Function
        (Ada_Node    => Ada_Node,
         Name        => Name,
         Binders     => New_Binders (Binders),
         Return_Type => Return_Type,
         Def         => Def);
   end New_Function;

   ------------------------
   -- New_Global_Binding --
   ------------------------

   function New_Global_Binding
     (Ada_Node : Node_Id := Empty;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array;
      Pre      : W_Predicate_Id := New_True_Literal_Pred;
      Def      : W_Prog_Id;
      Post     : W_Predicate_Id := New_True_Literal_Pred)
     return W_Declaration_Id is
   begin
      return New_Global_Binding
        (Ada_Node => Ada_Node,
         Name     => Name,
         Pre      => Pre,
         Binders  => New_Binders (Binders),
         Def      =>
           New_Post_Assertion
             (Prog => Def,
              Post => New_Postcondition (Pred => Post)));
   end New_Global_Binding;

   ---------------
   -- New_Logic --
   ---------------

   function New_Logic
     (Ada_Node    : Node_Id := Empty;
      Name        : W_Identifier_Id;
      Binders     : Binder_Array;
      Return_Type : W_Primitive_Type_Id)
     return W_Logic_Declaration_Class_Id is
   begin
      return New_Logic
        (Ada_Node   => Ada_Node,
         Names      => (1 => Name),
         Logic_Type =>
           New_Logic_Type
             (Arg_Types   => New_Binders (Binders),
              Return_Type => +Return_Type));
   end New_Logic;

   -------------------
   -- New_Parameter --
   -------------------

   function New_Parameter
     (Ada_Node    : Node_Id := Empty;
      Name        : W_Identifier_Id;
      Binders     : Binder_Array;
      Return_Type : W_Primitive_Type_Id;
      Effects     : W_Effects_Id := New_Effects;
      Pre         : W_Predicate_Id := New_True_Literal_Pred;
      Post        : W_Predicate_Id := New_True_Literal_Pred)
     return W_Declaration_Id is
   begin
      return New_Parameter_Declaration
        (Ada_Node       => Ada_Node,
         Names          => (1 => Name),
         Parameter_Type =>
           New_Computation_Type
             (Binders     => Binders,
              Return_Type => Return_Type,
              Pre         => Pre,
              Effects     => Effects,
              Post        => Post));
   end New_Parameter;

   ------------------------------
   -- New_Predicate_Definition --
   ------------------------------

   function New_Predicate_Definition
     (Ada_Node : Node_Id := Empty;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array;
      Def      : W_Predicate_Id)
     return W_Logic_Declaration_Class_Id is
   begin
      return New_Predicate_Definition
        (Ada_Node => Ada_Node,
         Name     => Name,
         Binders  => New_Binders (Binders),
         Def      => Def);
   end New_Predicate_Definition;

   --------------------
   -- New_Term_Array --
   --------------------

   function New_Term_Array (Binders : Binder_Array) return W_Term_Array is
      Result : W_Term_Array (Binders'Range);
   begin
      if Binders'Length = 0 then
         return (1 => New_Void_Literal);
      else
         for B in Binders'Range loop
            Result (B) := New_Term_Identifier (Name => Binders (B).B_Name);
         end loop;
      end if;

      return Result;
   end New_Term_Array;

   ---------------------------
   -- New_Universal_Quantif --
   ---------------------------

   function New_Universal_Quantif
     (Ada_Node : Node_Id := Empty;
      Binders  : Binder_Array;
      Pred     : W_Predicate_Id)
     return W_Predicate_Id is
   begin
      if Binders'Length = 0 then
         return Pred;
      else
         return New_Universal_Quantif
           (Ada_Node  => Ada_Node,
            Variables => (1 => Binders (Binders'First).B_Name),
            Var_Type  => Binders (Binders'First).B_Type,
            Pred      =>
              New_Universal_Quantif (Empty,
                                     Binders (Binders'First + 1
                                              .. Binders'Last),
                                     Pred));
      end if;
   end New_Universal_Quantif;

end Why.Gen.Binders;
