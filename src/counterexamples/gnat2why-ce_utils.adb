------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - C E _ U T I L S                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2018-2020, AdaCore                     --
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

with Ada.Strings.Fixed; use Ada.Strings.Fixed;
with Atree;
with Gnat2Why.Tables;   use Gnat2Why.Tables;
with Nlists;
with Sinput;            use Sinput;
with SPARK_Util;        use SPARK_Util;

package body Gnat2Why.CE_Utils is

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

   --------------------
   -- UI_From_String --
   --------------------

   function UI_From_String (Val : String) return Uint
   is
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
            return UI_Add (UI_Mul
                           (UI_From_String (Left),
                              UI_Expon (Uint_10, Int (Right'Length))),
                           UI_From_String (Right));
         end;
   end UI_From_String;

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

end Gnat2Why.CE_Utils;
