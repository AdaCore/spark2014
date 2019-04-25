------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - C E _ U T I L S                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2018-2019, AdaCore                     --
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

with Gnat2Why.Tables; use Gnat2Why.Tables;
with SPARK_Util;      use SPARK_Util;

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
            Lines_Map : Cntexample_Line_Maps.Map renames
              Element (File_C).Other_Lines;

         begin
            if not Is_All_Zeros_Line (Element (File_C).VC_Line) then
               return False;
            end if;

            for Line_C in Lines_Map.Iterate loop
               if not Is_All_Zeros_Line (Lines_Map (Line_C)) then
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

end Gnat2Why.CE_Utils;
