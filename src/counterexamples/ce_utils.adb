------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - C E _ U T I L S                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2018-2022, AdaCore                     --
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

with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;
with Ada.Strings.Fixed;           use Ada.Strings.Fixed;
with Ada.Strings.Unbounded;
with Atree;
with Gnat2Why.Tables;             use Gnat2Why.Tables;
with Nlists;                      use Nlists;
with Sinput;                      use Sinput;
with SPARK_Definition;            use SPARK_Definition;
with SPARK_Definition.Annotate;   use SPARK_Definition.Annotate;
with SPARK_Util;                  use SPARK_Util;

package body CE_Utils is

   function Compile_Time_Known_Value_Or_Aggr (Op : Node_Id) return Boolean;
   --  Similar to Compile_Time_Known_Value, but also returns True if the value
   --  is a compile-time-known aggregate, i.e. an aggregate all of whose
   --  constituent expressions are either compile-time-known values (based on
   --  calling Compile_Time_Known_Value) or compile-time-known aggregates.
   --  Note that the aggregate could still involve run-time checks that might
   --  fail (such as for subtype checks in component associations), but the
   --  evaluation of the expressions themselves will not raise an exception.
   --
   --  ??? This routine was originally reused from the frontend, but it
   --  was a relic VMS utility; it is highly unlikely we should use it for
   --  counterexamples.

   --------------------------------------
   -- Compile_Time_Known_Value_Or_Aggr --
   --------------------------------------

   function Compile_Time_Known_Value_Or_Aggr (Op : Node_Id) return Boolean is
   begin
      --  If we have an entity name, then see if it is the name of a constant
      --  and if so, test the corresponding constant value, or the name of
      --  an enumeration literal, which is always a constant.

      if Is_Entity_Name (Op) then
         declare
            E : constant Entity_Id := Entity (Op);
            V : Node_Id;

         begin
            if Ekind (E) = E_Enumeration_Literal then
               return True;

            elsif Ekind (E) /= E_Constant then
               return False;

            else
               V := Constant_Value (E);
               return Present (V)
                 and then Compile_Time_Known_Value_Or_Aggr (V);
            end if;
         end;

      --  We have a value, see if it is compile-time-known

      else
         if Compile_Time_Known_Value (Op) then
            return True;

         elsif Nkind (Op) = N_Aggregate then

            if Present (Expressions (Op)) then
               declare
                  Expr : Node_Id;
               begin
                  Expr := First (Expressions (Op));
                  while Present (Expr) loop
                     if not Compile_Time_Known_Value_Or_Aggr (Expr) then
                        return False;
                     else
                        Next (Expr);
                     end if;
                  end loop;
               end;
            end if;

            if Present (Component_Associations (Op)) then
               declare
                  Cass : Node_Id;

               begin
                  Cass := First (Component_Associations (Op));
                  while Present (Cass) loop
                     if not
                       Compile_Time_Known_Value_Or_Aggr (Expression (Cass))
                     then
                        return False;
                     end if;

                     Next (Cass);
                  end loop;
               end;
            end if;

            return True;

         elsif Nkind (Op) = N_Qualified_Expression then
            return Compile_Time_Known_Value_Or_Aggr (Expression (Op));

         --  All other types of values are not known at compile time

         else
            return False;
         end if;

      end if;
   end Compile_Time_Known_Value_Or_Aggr;

   -------------------------------------
   -- Compile_Time_Known_And_Constant --
   -------------------------------------

   function Compile_Time_Known_And_Constant
     (E : Entity_Id) return Boolean
   is
   begin
      if Ekind (E) = E_Constant then
         declare
            Decl : constant Node_Id := Enclosing_Declaration (E);
            Expr : constant Node_Id := Expression (Decl);
         begin
            return Present (Expr)
              and then Compile_Time_Known_Value_Or_Aggr (Expr);
         end;
      end if;

      return False;
   end Compile_Time_Known_And_Constant;

   ----------------------------------
   -- Component_Is_Removed_In_Type --
   ----------------------------------

   function Component_Is_Removed_In_Type
     (Ty   : Entity_Id;
      Comp : Entity_Id;
      Vals : Entity_To_Value_Maps.Map) return Boolean
   is

      function Eval_Discrete_Choices
        (Choices : List_Id;
         Discr   : Big_Integer) return Boolean;
      --  Evaluate Discr in Choices assuming Choices contains only static
      --  values.

      function Eval_Others_Choice
        (Info   : Component_Info;
         Discr  : Big_Integer) return Boolean;
      --  Return True is Discr in Choices returns True for all Choices in
      --  Info.Parent_Var_Part, assuming all the choices contains only static
      --  values.

      ---------------------------
      -- Eval_Discrete_Choices --
      ---------------------------

      function Eval_Discrete_Choices
        (Choices : List_Id;
         Discr   : Big_Integer) return Boolean
      is
         Choice : Node_Id := First (Choices);
      begin
         while Present (Choice) loop
            pragma Assert (Nkind (Choice) /= N_Others_Choice);

            --  When the choice denotes a subtype with a predicate, check the
            --  expression against the predicate values.

            if (Nkind (Choice) = N_Subtype_Indication
                or else (Is_Entity_Name (Choice)
                         and then Is_Type (Entity (Choice))))
              and then Has_Predicates (Etype (Choice))
            then
               pragma Assert (Has_Static_Predicate (Etype (Choice)));
               if Eval_Discrete_Choices
                 (Static_Discrete_Predicate (Etype (Choice)), Discr)
               then
                  return True;
               end if;

            --  The bounds of the range should be compile time known as only
            --  static choices are allowed in variant parts.

            elsif Nkind (Choice) in N_Subtype_Indication | N_Range
              or else (Is_Entity_Name (Choice)
                       and then Is_Type (Entity (Choice)))
            then
               declare
                  Range_Node : constant Node_Id := Get_Range (Choice);
                  Low        : constant Node_Id := Low_Bound (Range_Node);
                  High       : constant Node_Id := High_Bound (Range_Node);
                  Fst, Lst   : Big_Integer;
               begin
                  pragma Assert (Compile_Time_Known_Value (Low)
                                 and then Compile_Time_Known_Value (High));
                  Fst := From_String (UI_Image (Expr_Value (Low)));
                  Lst := From_String (UI_Image (Expr_Value (High)));

                  if Discr >= Fst and then Lst >= Discr then
                     return True;
                  end if;
               end;

            --  Single value choices should be compile time known as only
            --  static choices are allowed in variant parts.

            else
               declare
                  Val : Big_Integer;
               begin
                  pragma Assert (Compile_Time_Known_Value (Choice));
                  Val := From_String (UI_Image (Expr_Value (Choice)));
                  if Discr = Val then
                     return True;
                  end if;
               end;
            end if;

            Next (Choice);
         end loop;

         return False;
      end Eval_Discrete_Choices;

      ------------------------
      -- Eval_Others_Choice --
      ------------------------

      function Eval_Others_Choice
        (Info   : Component_Info;
         Discr  : Big_Integer) return Boolean
      is
         Var_Part : constant Node_Id := Info.Parent_Var_Part;
         Var      : Node_Id := First (Variants (Var_Part));

      begin
         while Present (Var) loop
            if not Is_Others_Choice (Discrete_Choices (Var))
              and then Eval_Discrete_Choices (Discrete_Choices (Var), Discr)
            then
               return False;
            end if;
            Next (Var);
         end loop;

         return True;
      end Eval_Others_Choice;

      use Entity_To_Value_Maps;
      Comp_Info : constant Component_Info_Map := Get_Variant_Info (Ty);
      Info      : Component_Info;

   --  Start of processing for Component_Is_Removed_In_Type

   begin
      --  If Comp is not a component, it cannot be discriminant dependant

      if Ekind (Comp) /= E_Component then
         return False;
      end if;

      --  Go through the enclosing variant parts if any to check the value of
      --  the corresponding discriminants.

      Info := Get_Component_Info (Comp_Info, Comp);

      while Present (Info.Parent_Variant) loop
         declare
            Discr   : constant Node_Id :=
              Entity (Name (Info.Parent_Var_Part));
            Cur     : constant Entity_To_Value_Maps.Cursor :=
              Vals.Find (Discr);
            Val     : Value_Type;
            Int_Val : Big_Integer;

         begin
            --  If we do not have a counterexample value for Discr, the
            --  component cannot be removed. Go to the next variant part in
            --  case it uses another discriminant.

            if Cur = No_Element then
               goto Next_Variant;
            end if;

            Val := Element (Cur).all;
            pragma Assert (Val.K = Scalar_K);

            if Val.Scalar_Content = null then
               goto Next_Variant;
            end if;

            --  Transform the counterexample value of Discr into a big integer

            case Val.Scalar_Content.K is
               when Integer_K =>
                  Int_Val := Val.Scalar_Content.Integer_Content;

               when Enum_K =>
                  declare
                     Ent : constant Entity_Id :=
                       Val.Scalar_Content.Enum_Entity;
                  begin
                     if Nkind (Ent) = N_Character_Literal then
                        Int_Val := From_String
                          (UI_Image (Char_Literal_Value (Ent)));
                     else
                        pragma Assert (Ekind (Ent) = E_Enumeration_Literal);
                        Int_Val := From_String
                          (UI_Image (Enumeration_Pos (Ent)));
                     end if;
                  end;
               when others =>
                  raise Program_Error;
            end case;

            --  Check the necessary contraint on Discr for Comp to be defined.
            --  If it is False, the component can be removed.

            declare
               Cond : constant Boolean :=
                 (if Is_Others_Choice (Discrete_Choices (Info.Parent_Variant))
                  then Eval_Others_Choice (Info, Int_Val)
                  else Eval_Discrete_Choices
                    (Discrete_Choices (Info.Parent_Variant), Int_Val));
            begin
               if not Cond then
                  return True;
               end if;
            end;

            --  The component could not be excluded looking at the value of the
            --  first enclosing variant part. Go to the enclosing one if any.

            <<Next_Variant>>
            Info := Get_Component_Info (Comp_Info, Info.Parent_Var_Part);
         end;
      end loop;

      return False;
   end Component_Is_Removed_In_Type;

   -------------------------------
   -- Compute_Filename_Previous --
   -------------------------------

   function Compute_Filename_Previous (Filename    : String;
                                       Is_Previous : out Boolean;
                                       Ada_Node    : in out Node_Id)
                                       return String
   is

      Match : constant String := "'@Loop";
   begin
      if Filename'Length >= Match'Length and then
        Filename (Filename'First .. Filename'First + Match'Length - 1) =
        Match
      then
         declare
            Number_At_Tick : constant Natural :=
              Index (Source  => Filename (Filename'First + Match'Length ..
                       Filename'Last),
                     Pattern => "'");
         begin
            Ada_Node :=
              Get_Entity_Id (False,
                             Filename (Filename'First + Match'Length ..
                                   Number_At_Tick - 2));
            Is_Previous := True;
            return Filename (Number_At_Tick + 1 .. Filename'Last);
         end;
      else
         Is_Previous := False;
         return Filename;
      end if;
   end Compute_Filename_Previous;

   ------------------
   -- Convert_Node --
   ------------------

   function Convert_Node (N : Integer) return Node_Id is
   begin
      return Node_Id (N);
   exception
      when others => return Empty;
   end Convert_Node;

   -----------------------------
   -- Find_First_Static_Range --
   -----------------------------

   procedure Find_First_Static_Range
     (N   : Node_Id;
      Fst : out Uint;
      Lst : out Uint)
   is
      Fst_Found, Lst_Found : Boolean := False;
      Current              : Node_Id := N;

   begin
      --  Initialize outputs with dummy values that will be rewritten in the
      --  loop, to facilitate static analysis.

      Fst := Uint_0;
      Lst := Uint_0;

      loop
         declare
            Rng  : constant Node_Id := Get_Range (Current);
            Low  : constant Node_Id := Low_Bound (Rng);
            High : constant Node_Id := High_Bound (Rng);
         begin
            if not Fst_Found and then Compile_Time_Known_Value (Low) then
               Fst := Expr_Value (Low);
               Fst_Found := True;
            end if;
            if not Lst_Found and then Compile_Time_Known_Value (High) then
               Lst := Expr_Value (High);
               Lst_Found := True;
            end if;
         end;
         exit when Fst_Found and Lst_Found;

         Current := Retysp (Etype (Current));
      end loop;
   end Find_First_Static_Range;

   -------------------
   -- Get_Entity_Id --
   -------------------

   function Get_Entity_Id (Is_Record : Boolean; S : String) return Entity_Id is
      I : constant Integer := (if Is_Record then 1 else 0);
   begin
      if S'First + I > S'Last then
         return Empty;
      else
         return Entity_Id'Value (S (S'First + I .. S'Last));
      end if;
   exception
      when Constraint_Error =>
         return Empty;
   end Get_Entity_Id;

   ---------------------------
   -- Is_Nul_Counterexample --
   ---------------------------

   function Is_Nul_Counterexample
     (Cntexmp : Cntexample_File_Maps.Map) return Boolean
   is
      use Cntexample_File_Maps;
      function Is_All_Zeros_Line
        (Line : Cntexample_Elt_Lists.List) return Boolean
      is
        (for all Elt of Line => Elt.Val_Str.Nul);

   begin
      for File_C in Cntexmp.Iterate loop
         declare
            Lines_Map    : Cntexample_Line_Maps.Map renames
                             Element (File_C).Other_Lines;
            Previous_Map : Previous_Line_Maps.Map renames
                             Element (File_C).Previous_Lines;

         begin
            if not Is_All_Zeros_Line (Element (File_C).VC_Line) then
               return False;
            end if;

            for Line_C in Lines_Map.Iterate loop
               if not Is_All_Zeros_Line (Lines_Map (Line_C)) then
                  return False;
               end if;
            end loop;

            for Line_C in Previous_Map.Iterate loop
               if not Is_All_Zeros_Line (Previous_Map (Line_C).Line_Cnt) then
                  return False;
               end if;
            end loop;
         end;
      end loop;

      return True;
   end Is_Nul_Counterexample;

   ------------------------
   -- Is_Visible_In_Type --
   ------------------------

   --  Body intentionally hidden from spec file
   function Is_Visible_In_Type (Rec  : Entity_Id;
                                Comp : Entity_Id)
                                return Boolean
   is
     (Ekind (Comp) = E_Discriminant
      or else (not Is_Type (Comp)
               and then Component_Is_Present_In_Type
                 (Rec, Search_Component_In_Type (Rec, Comp))));

   ---------------------
   -- Prefix_Elements --
   ---------------------

   function Prefix_Elements
     (Elems : S_String_List.List;
      Pref  : String) return S_String_List.List
   is
      use Ada.Strings.Unbounded;
      L : S_String_List.List;
   begin
      for E of Elems loop
         L.Append (Pref & E);
      end loop;
      return L;
   end Prefix_Elements;

   -----------------
   -- Remove_Vars --
   -----------------

   package body Remove_Vars is

      function Get_Line_Encapsulating_Function (A : Node_Id) return Natural
        with Pre => Nkind (A) = N_Pragma;
      --  Get the line of the definition of the function in which a
      --  Loop_Invariant is defined.

      function Get_Line_Encapsulating_Loop (A : Node_Id) return Natural
        with Pre => Nkind (A) = N_Pragma;
      --  Get the line of the definition of the directly encapsulating loop of
      --  a Loop_Invariant.

      procedure Eliminate_Between (Other_Lines : out Cntexample_Line_Maps.Map;
                                   Previous_Line :
                                   Cntexample_Elt_Lists.List;
                                   Node                   : Integer);
      --  Eliminate the counterexamples variables that are present in
      --  Previous_Line from Other_Lines. These should have a location between
      --  the encapsulating function of Node and the encapsulating loop of
      --  Node. These are known to be duplicates of the Previous_Line.

      ---------------------------------
      -- Get_Line_Encapsulating_Loop --
      ---------------------------------

      function Get_Line_Encapsulating_Loop (A : Node_Id) return Natural is

         function Is_Loop_Stmt (N : Node_Id) return Boolean is
           (Nkind (N) = N_Loop_Statement);

         function Enclosing_Loop_Stmt is new
           First_Parent_With_Property (Is_Loop_Stmt);

         --  Parent_Node should point to the loop statement
         Parent_Node : constant Node_Id := Enclosing_Loop_Stmt (A);
      begin
         if Nlists.Is_List_Member (Parent_Node) then
            declare
               Prev_Parent : constant Node_Id := Nlists.Prev (Parent_Node);
            begin
               if Present (Prev_Parent) then
                  return Natural
                    (Get_Logical_Line_Number (Sloc (Prev_Parent)));
               else
                  --  Loop is the first statement so we try to return just
                  --  before the N_Handled_Sequence_Of_Statements (to avoid
                  --  removing data from the loop).
                  return Natural (Get_Logical_Line_Number
                                  (Sloc (Atree.Parent (Parent_Node)))) - 1;
               end if;
            end;
         else
            return Natural (Get_Logical_Line_Number
                            (Sloc (Atree.Parent (Parent_Node))));
         end if;
      exception
         when others => return 0;
      end Get_Line_Encapsulating_Loop;

      -------------------------------------
      -- Get_Line_Encapsulating_Function --
      -------------------------------------

      function Get_Line_Encapsulating_Function (A : Node_Id) return Natural is
      begin
         return Natural (Get_Logical_Line_Number (Sloc
                         (Directly_Enclosing_Subprogram_Or_Entry (A))));
      exception
         when others => return 0;
      end Get_Line_Encapsulating_Function;

      -----------------------
      -- Eliminate_Between --
      -----------------------

      procedure Eliminate_Between (Other_Lines   :
                                     out Cntexample_Line_Maps.Map;
                                   Previous_Line :
                                     Cntexample_Elt_Lists.List;
                                   Node          : Integer)
      is
         Node_LI : constant Node_Id := Convert_Node (Node);
         B       : constant Natural :=
           Get_Line_Encapsulating_Function (Node_LI);
         E       : constant Natural := Get_Line_Encapsulating_Loop (Node_LI);
         use Cntexample_Elt_Lists;
         use Cntexample_Line_Maps;
         New_Lines : Cntexample_Line_Maps.Map := Empty_Map;
      begin
         for C in Other_Lines.Iterate loop
            declare
               Line_Variables : Cntexample_Elt_Lists.List := Element (C);
               Line_Number    : Natural renames Key (C);
            begin
               if Line_Number >= B and then Line_Number <= E then
                  for V in Previous_Line.Iterate loop
                     declare
                        Cur : Cntexample_Elt_Lists.Cursor :=
                                Cntexample_Elt_Lists.Find (Line_Variables,
                                                           Element (V));
                     begin
                        if Has_Element (Cur) then
                           Line_Variables.Delete (Cur);
                        end if;
                     end;
                  end loop;
               end if;
               if not Is_Empty (Line_Variables) then
                  New_Lines.Include (Line_Number, Line_Variables);
               end if;
            end;
         end loop;
         Other_Lines := New_Lines;
      end Eliminate_Between;

      -----------------------
      -- Remove_Extra_Vars --
      -----------------------

      procedure Remove_Extra_Vars (Cntexmp : in out Cntexample_File_Maps.Map)
      is
      --  Here we assume that Create_Pretty_Cntexmp just was used. So, there is
      --  a complete counterexample with, in particular, Previous_Lines filled
      --  and other lines all filled.
      begin
         for Fcur in Cntexmp.Iterate loop
            declare
               File : Cntexample_Lines :=
                 Cntexample_File_Maps.Element
                          (Cntexmp,
                           Cntexample_File_Maps.Key (Fcur));
               Previous_Loc : Previous_Line_Maps.Map renames
                                File.Previous_Lines;

            begin
               for C in Previous_Loc.Iterate loop
                  declare
                     Previous_Elt : constant Previous_Line :=
                       Previous_Loc.Element (Previous_Line_Maps.Key (C));
                     Node_LI      : constant Integer :=
                       Previous_Elt.Ada_Node;
                  begin
                     Eliminate_Between (File.Other_Lines,
                                        Previous_Elt.Line_Cnt,
                                        Node_LI);
                  end;
               end loop;
               Cntexmp.Replace_Element (Fcur, File);
            end;
         end loop;
      end Remove_Extra_Vars;

   end Remove_Vars;

   --------------------
   -- UI_From_String --
   --------------------

   function UI_From_String (Val : String) return Uint is
   begin
      --  Try to cast Val to Int if it fits

      return UI_From_Int (Int'Value (Val));
   exception

      --  If it doesn't fit, cut Val in two substrings and retry

      when Constraint_Error =>

         --  Avoid looping in case of an illformed string

         if Val'Length < 2 then
            raise;
         end if;

         declare
            Cut   : constant Positive := Val'First + Val'Length / 2;
            Left  : String renames Val (Val'First .. Cut);
            Right : String renames Val (Cut + 1 .. Val'Last);
         begin
            return
              UI_From_String (Left) * Uint_10 ** Int (Right'Length)
                +
              UI_From_String (Right);
         end;
   end UI_From_String;

   --------------------------
   -- Ultimate_Cursor_Type --
   --------------------------

   function Ultimate_Cursor_Type (Typ : Entity_Id) return Entity_Id is
      Found         : Boolean;
      Iterable_Info : Iterable_Annotation;

   begin
      --  Iteration is done on the cursor type of the ultimate model for
      --  proof. Go through Iterable_For_Proof annotations to find this
      --  type.

      Retrieve_Iterable_Annotation (Typ, Found, Iterable_Info);

      if Found then

         --  Iterable annotation should be a Model annotation. Indeed, if
         --  a Contains iterable annotation is provided, no temporary
         --  should be introduced for "for of" quantification.

         pragma Assert
           (Iterable_Info.Kind = SPARK_Definition.Annotate.Model);

         --  Prepend the name of the Model function to the container name
         --  and refine value on model type.

         return Ultimate_Cursor_Type (Etype (Iterable_Info.Entity));
      else

         --  We have found the ultimate model type. Quantification is
         --  done on its cursor type.

         return Get_Cursor_Type (Typ);
      end if;
   end Ultimate_Cursor_Type;

end CE_Utils;
