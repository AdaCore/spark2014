------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              G N A T 2 W H Y _ C O U N T E R _ E X A M P L E S           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2016-2026, AdaCore                     --
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

with Ada.Containers.Ordered_Sets;
with Ada.Strings.Unbounded;       use Ada.Strings.Unbounded;
with Atree;
with CE_Interval_Sets;
with CE_Parsing;                  use CE_Parsing;
with CE_Pretty_Printing;          use CE_Pretty_Printing;
with CE_RAC;                      use CE_RAC;
with CE_Utils;                    use CE_Utils;
with Elists;                      use Elists;
with Erroutc;                     use Erroutc;
with Flow_Types;                  use Flow_Types;
with Flow_Utility;                use Flow_Utility;
with Flow_Utility.Initialization; use Flow_Utility.Initialization;
with Gnat2Why_Args;
with Gnat2Why_Opts;               use Gnat2Why_Opts;
with Gnat2Why.Util;               use Gnat2Why.Util;
with Namet;
with Nlists;                      use Nlists;
with Sinput;                      use Sinput;
with Snames;                      use Snames;
with SPARK_Atree;                 use SPARK_Atree;
with SPARK_Atree.Entities;        use SPARK_Atree.Entities;
with SPARK_Definition.Annotate;   use SPARK_Definition.Annotate;
with SPARK_Util;                  use SPARK_Util;
with SPARK_Util.Types;            use SPARK_Util.Types;
with String_Utils;                use String_Utils;

package body CE_Display is

   procedure Before_Next_Element (Str : in out Unbounded_String);
   --  Action on Str before printing the next element

   function Remap_VC_Info
     (Cntexmp : Cntexample_File_Maps.Map; VC_File : String; VC_Line : Natural)
      return Cntexample_File_Maps.Map;
   --  Map counterexample information related to the current VC to the
   --  location of the check in the Ada file.
   --  In Cntexmp, this information is mapped to the field "vc_line" of the
   --  JSON object representing the file where the construct is located.

   function Remove_Irrelevant_Branches
     (Cntexmp : Cntexample_File_Maps.Map) return Cntexample_File_Maps.Map;
   --  Remove counterexample branches that are not taken

   function Is_Ada_File_Name (File : String) return Boolean;
   --  check if the filename is an Ada
   --  ??? This check is wrong, need to get rid of it

   function Is_Uninitialized
     (Element_Decl : Entity_Id; Element_File : String; Element_Line : Natural)
      return Boolean
   with Pre => Nkind (Element_Decl) in N_Entity;
   --  Return True if the counterexample element with given declaration at
   --  given position is uninitialized.

   function Compare_Name (X, Y : Entity_Id) return Boolean
   is (Raw_Source_Name (X) < Raw_Source_Name (Y)
       or else (Raw_Source_Name (X) = Raw_Source_Name (Y) and then X < Y));
   --  Variables are stored in alphabetical order. Compare the entity id in
   --  case there are homonyms.

   function Get_Cntexmp_Line_Str
     (Cntexmp_Line : Cntexample_Elt_Lists.List) return String;
   --  Reconstruct a string from a pretty printed one line counterexample

   package Name_Ordered_Entities_Sets is new
     Ada.Containers.Ordered_Sets
       (Element_Type => Entity_Id,
        "<"          => Compare_Name);

   procedure Build_Pretty_Line
     (Variables               : Entity_To_Extended_Value_Maps.Map;
      File                    : String;
      Line                    : Natural;
      Pretty_Line_Cntexmp_Arr : out Cntexample_Elt_Lists.List;
      Is_Json_Format          : Boolean := False);
   --  Build pretty printed JSON array of counterexample elements.
   --  @Variables stores information about values and fields of
   --    variables at a single source code location (line).

   function Reconstruct_Index_Value
     (Value : Unbounded_String; Quant_Id : Entity_Id) return Unbounded_String;
   --  Reconstruct a string for the value of the Ada quantified variable
   --  in a FOR OF quantification from the value for the Why3 quantified
   --  variable.

   generic
      with
        procedure Process_Entity
          (E : Entity_Id; Mode : Modifier; Loop_Id : Entity_Id := Empty);
   procedure Process_Entities_For_One_Liner (N : Node_Id; K : VC_Kind);
   --  Traverse the node N related to a one liner and call Process_Entity on
   --  all relevant entities. Loop_Id is set to the relevant loop when Mode is
   --  Loop_Entry.

   -------------------------
   -- Before_Next_Element --
   -------------------------

   procedure Before_Next_Element (Str : in out Unbounded_String) is
   begin
      if Str /= "" then
         --  When outputting counterexamples on the command-line in
         --  pretty mode, display each value on a separate line.

         if Gnat2Why_Args.Output_Mode in GPO_Pretty then
            Append (Str, ASCII.LF & SGR_Note & "      and " & SGR_Reset);
         else
            Append (Str, " and ");
         end if;
      end if;
   end Before_Next_Element;

   -----------------------
   -- Build_Pretty_Line --
   -----------------------

   procedure Build_Pretty_Line
     (Variables               : Entity_To_Extended_Value_Maps.Map;
      File                    : String;
      Line                    : Natural;
      Pretty_Line_Cntexmp_Arr : out Cntexample_Elt_Lists.List;
      Is_Json_Format          : Boolean := False)
   is
      use Entity_To_Extended_Value_Maps;
      Ordered_Variables : Name_Ordered_Entities_Sets.Set;

      --  Start of processing for Build_Pretty_Line

   begin
      Pretty_Line_Cntexmp_Arr := Cntexample_Elt_Lists.Empty_List;

      --  Insert elements of Variables in an ordered set to print them in order

      for C_Var in Variables.Iterate loop
         declare
            Var_Id : constant Entity_Id := Key (C_Var);

         begin
            --  Do not consider compile time known constants and uninitialized
            --  variables.

            if not Is_Uninitialized (Var_Id, File, Line)
              and then not Compile_Time_Known_And_Constant (Var_Id)
            then
               Ordered_Variables.Insert (Var_Id);
            end if;
         end;
      end loop;

      for Var of Ordered_Variables loop
         declare
            Values   : Extended_Value_Access renames Variables (Var);
            Var_Name : constant String := Raw_Source_Name (Var);
            Value    : Value_Type;
            Name     : Unbounded_String;
         begin
            for Var_Mod in Modifier loop
               Name := To_Unbounded_String (Var_Name);

               --  Update the name with the modifier

               case Var_Mod is
                  when None | Index     =>
                     null;

                  when Old              =>
                     Append (Name, "'Old");

                  when Loop_Entry       =>
                     Append (Name, "'Loop_Entry");

                  when CE_Values.Result =>
                     Append (Name, "'Result");
               end case;

               if Values (Var_Mod) /= null then
                  Value := Values (Var_Mod).all;

                  --  Special case for the Index modifier. Get the value of
                  --  the counterexample as a string and reconstruct the
                  --  Ada quantified value above it.

                  if Var_Mod = Index then
                     declare
                        Pretty_Value : CNT_Unbounded_String :=
                          Print_Value (Value);

                     begin
                        if Pretty_Value /= Dont_Display then
                           if Is_Json_Format then
                              Pretty_Line_Cntexmp_Arr.Append
                                (Cntexample_Elt'
                                   (K        => Json_Format,
                                    Kind     => CEE_Variable,
                                    Name     => Name,
                                    JSON_Obj => Serialize_Value (Value)));
                           else
                              Pretty_Value.Str :=
                                Reconstruct_Index_Value
                                  (Pretty_Value.Str, Var);

                              Pretty_Line_Cntexmp_Arr.Append
                                (Cntexample_Elt'
                                   (K       => Pretty_Printed,
                                    Kind    => CEE_Variable,
                                    Name    => Name,
                                    Val_Str => Pretty_Value));
                           end if;
                        end if;
                     end;

                  --  General case, add the counterexample value and its
                  --  attributes.

                  else
                     --  For non null access values, write X.all = Value
                     --  instead of X = new T'(Value) at top level.

                     if Value.K = Access_K
                       and then Value.Designated_Value /= null
                       and then
                         (not Value.Is_Null.Present
                          or else not Value.Is_Null.Content)
                     then
                        Append (Name, ".all");
                        Value := Value.Designated_Value.all;
                     end if;

                     Print_Value_And_Attributes
                       (Name, Value, Pretty_Line_Cntexmp_Arr, Is_Json_Format);
                  end if;
               end if;
            end loop;
         end;
      end loop;
   end Build_Pretty_Line;

   ---------------------------
   -- Create_Pretty_Cntexmp --
   ---------------------------

   function Create_Pretty_Cntexmp
     (Cntexmp : Cntexample_File_Maps.Map;
      VC_Loc  : Source_Ptr;
      VC_Node : Node_Id;
      VC_K    : VC_Kind;
      Subp    : Entity_Id) return Cntexample_Data
   is
      use Cntexample_File_Maps;

      procedure Create_Pretty_Line
        (Pretty_File_Cntexmp : in out Cntexample_Lines;
         File                : String;
         Line                : Natural;
         Line_Cntexmp        : Cntexample_Elt_Lists.List;
         Is_Previous         : Boolean;
         LI_Node             : Node_Id;
         Is_One_Liner        : Boolean);
      --  Pretty prints counterexample model elements at a single source
      --  code location (line).

      ------------------------
      -- Create_Pretty_Line --
      ------------------------

      procedure Create_Pretty_Line
        (Pretty_File_Cntexmp : in out Cntexample_Lines;
         File                : String;
         Line                : Natural;
         Line_Cntexmp        : Cntexample_Elt_Lists.List;
         Is_Previous         : Boolean;
         LI_Node             : Node_Id;
         Is_One_Liner        : Boolean)
      is
         Variables               : Entity_To_Extended_Value_Maps.Map;
         Pretty_Line_Cntexmp_Arr : Cntexample_Elt_Lists.List;

         --  Start of processing for Create_Pretty_Line

      begin
         Parse_Counterexample_Line (Line_Cntexmp, Variables);

         --  On the one liner, we need to filter relevant nodes

         if Is_One_Liner then
            declare
               Tmp_Vars : Entity_To_Extended_Value_Maps.Map;

               procedure Pick_Relevant_Variable
                 (E       : Entity_Id;
                  Mode    : Modifier;
                  Loop_Id : Entity_Id := Types.Empty);
               --  Get counterexample value for the entity E with mode Mode
               --  from Tmp_Vars and store it in Variables.

               ----------------------------
               -- Pick_Relevant_Variable --
               ----------------------------

               procedure Pick_Relevant_Variable
                 (E       : Entity_Id;
                  Mode    : Modifier;
                  Loop_Id : Entity_Id := Types.Empty)
               is
                  pragma Unreferenced (Loop_Id);
                  Pos      : Entity_To_Extended_Value_Maps.Cursor;
                  Tmp_Pos  : Entity_To_Extended_Value_Maps.Cursor :=
                    Tmp_Vars.Find (E);
                  Inserted : Boolean;
               begin
                  if Entity_To_Extended_Value_Maps.Has_Element (Tmp_Pos) then
                     Variables.Insert (E, (others => null), Pos, Inserted);
                     Variables (Pos) (Mode) := Tmp_Vars (Tmp_Pos) (Mode);
                  end if;
               end Pick_Relevant_Variable;

               procedure Pick_Relevant_Variables is new
                 Process_Entities_For_One_Liner (Pick_Relevant_Variable);
            begin
               Tmp_Vars.Move (Variables);
               Pick_Relevant_Variables (VC_Node, VC_K);
            end;
         end if;

         if not Variables.Is_Empty then
            Build_Pretty_Line (Variables, File, Line, Pretty_Line_Cntexmp_Arr);

            --  Add the counterexample line only if there are some pretty
            --  printed counterexample elements. Due to inlining, and because
            --  only a single line number is currently used in Line, we may end
            --  up with multiple counterexample values for the same value of
            --  Line. In such a case, the last value encountered is kept by
            --  using Include below.

            if not Pretty_Line_Cntexmp_Arr.Is_Empty then
               if Is_Previous then
                  Pretty_File_Cntexmp.Previous_Lines.Include
                    (Line,
                     (Line_Cnt => Pretty_Line_Cntexmp_Arr,
                      Ada_Node => Integer (LI_Node)));
               else
                  Pretty_File_Cntexmp.Other_Lines.Include
                    (Line, Pretty_Line_Cntexmp_Arr);
               end if;
            end if;
         end if;
      end Create_Pretty_Line;

      --  Local variables

      VC_File          : constant String := File_Name (VC_Loc);
      VC_Line          : constant Natural :=
        Natural (Get_Logical_Line_Number (VC_Loc));
      Remapped_Cntexmp : constant Cntexample_File_Maps.Map :=
        Remove_Irrelevant_Branches (Remap_VC_Info (Cntexmp, VC_File, VC_Line));
      Pretty_Cntexmp   : Cntexample_File_Maps.Map :=
        Cntexample_File_Maps.Empty_Map;

      Init_Loc  : constant Source_Ptr := Sloc (Subp);
      Init_File : constant String := File_Name (Init_Loc);
      Init_Line : constant Natural :=
        Natural (Get_Logical_Line_Number (Init_Loc));

      --  Inputs of the subprogram in json format.
      --  They are located on the subprogram declaration.
      Init_Cntexmp_Line : Cntexample_Elt_Lists.List;

      Variables : Entity_To_Extended_Value_Maps.Map;

      --  Start of processing for Create_Pretty_Cntexmp

   begin
      for File_C in Remapped_Cntexmp.Iterate loop
         declare
            Is_Previous         : Boolean;
            LI_Node             : Node_Id := Types.Empty;
            File                : constant String :=
              Compute_Filename_Previous (Key (File_C), Is_Previous, LI_Node);
            Pretty_File_Cntexmp : Cntexample_Lines :=
              (if No_Element /= Pretty_Cntexmp.Find (File)
               then Element (Pretty_Cntexmp.Find (File))
               else
                 Cntexample_Lines'
                   (VC_Line        => Cntexample_Elt_Lists.Empty_List,
                    Other_Lines    => Cntexample_Line_Maps.Empty_Map,
                    Previous_Lines => Previous_Line_Maps.Empty_Map));
            Lines_Map           : Cntexample_Line_Maps.Map renames
              Element (File_C).Other_Lines;

         begin
            for Line_C in Lines_Map.Iterate loop
               declare
                  Line : constant Natural := Cntexample_Line_Maps.Key (Line_C);
               begin
                  Create_Pretty_Line
                    (Pretty_File_Cntexmp,
                     File,
                     Line,
                     Lines_Map (Line_C),
                     Is_Previous,
                     LI_Node,
                     Is_One_Liner => File = VC_File and Line = VC_Line);

                  --  If the current Line is the one where the original
                  --  subprogram is declared, save it in Init_Cntexmp_Line

                  if File = Init_File and Line = Init_Line then
                     Parse_Counterexample_Line (Lines_Map (Line_C), Variables);

                     if not Variables.Is_Empty then
                        Build_Pretty_Line
                          (Variables,
                           Init_File,
                           Init_Line,
                           Is_Json_Format          => True,
                           Pretty_Line_Cntexmp_Arr => Init_Cntexmp_Line);
                     end if;
                  end if;
               end;
            end loop;

            --  At this point, the information of VC_line is now in the
            --  Other_Lines field because Remap_VC_Info was applied.
            if Is_Ada_File_Name (File)
              and then
                (not Cntexample_Line_Maps.Is_Empty
                       (Pretty_File_Cntexmp.Other_Lines)
                 or else
                   not Previous_Line_Maps.Is_Empty
                         (Pretty_File_Cntexmp.Previous_Lines))
            then
               Pretty_Cntexmp.Include (File, Pretty_File_Cntexmp);
            end if;
         end;
      end loop;

      Remove_Vars.Remove_Extra_Vars (Pretty_Cntexmp);

      return
        Cntexample_Data'
          (Pretty_Cntexmp,
           Json_Formatted_Input'
             (Init_Cntexmp_Line, To_Unbounded_String (Init_File), Init_Line));

   end Create_Pretty_Cntexmp;

   --------------------------
   -- Get_Cntexmp_Line_Str --
   --------------------------

   function Get_Cntexmp_Line_Str
     (Cntexmp_Line : Cntexample_Elt_Lists.List) return String
   is

      Cntexmp_Line_Str : Unbounded_String;

   begin
      for Elt of Cntexmp_Line loop
         if Elt.Kind /= CEE_Error_Msg then
            Before_Next_Element (Cntexmp_Line_Str);
            Append (Cntexmp_Line_Str, Elt.Name);
            Append (Cntexmp_Line_Str, " = ");
            Append (Cntexmp_Line_Str, Elt.Val_Str.Str);
         end if;
      end loop;
      return To_String (Cntexmp_Line_Str);
   end Get_Cntexmp_Line_Str;

   ---------------------------
   -- Get_Cntexmp_One_Liner --
   ---------------------------

   function Get_Cntexmp_One_Liner
     (Cntexmp : Cntexample_File_Maps.Map; VC_Loc : Source_Ptr) return String
   is
      File         : constant String := File_Name (VC_Loc);
      Line         : constant Logical_Line_Number :=
        Get_Logical_Line_Number (VC_Loc);
      File_Cur     : constant Cntexample_File_Maps.Cursor :=
        Cntexmp.Find (File);
      Cntexmp_Line : Cntexample_Elt_Lists.List :=
        Cntexample_Elt_Lists.Empty_List;

      --  Start of processing for Get_Cntexmp_One_Liner

   begin
      if Cntexample_File_Maps.Has_Element (File_Cur) then
         declare
            Line_Map : Cntexample_Line_Maps.Map renames
              Cntexmp (File_Cur).Other_Lines;
            Line_Cur : constant Cntexample_Line_Maps.Cursor :=
              Line_Map.Find (Natural (Line));
         begin
            if Cntexample_Line_Maps.Has_Element (Line_Cur) then
               Cntexmp_Line := Line_Map (Line_Cur);
            end if;
         end;
      end if;
      return Get_Cntexmp_Line_Str (Cntexmp_Line);
   end Get_Cntexmp_One_Liner;

   ------------------------
   -- Get_Environment_CE --
   ------------------------

   function Get_Environment_CE
     (N : Node_Id; K : VC_Kind; Subp : Node_Id) return Cntexample_Data
   is
      Expl          : Entity_To_Extended_Value_Maps.Map;
      Input_As_JSON : Json_Formatted_Input;

      procedure Insert_Expl (E : Entity_Id; V : Value_Type; Mode : Modifier);
      --  Insert a single value in Expl

      procedure Accumulate_Expl_For_Entity
        (E : Entity_Id; Mode : Modifier; Loop_Id : Entity_Id := Empty)
      with Pre => Mode = Loop_Entry or Loop_Id = Empty;
      --  Insert the value associated to E into Expl

      function Is_Internal_Entity (E : Entity_Id) return Boolean
      is (Is_Internal (E)
          or else
            (Nkind (E) in N_Has_Chars
             and then Namet.Is_Internal_Name (Chars (E))));

      procedure Insert_Cntexmp_Line
        (File    : String;
         Line    : Natural;
         Value   : in out Cntexample_Elt_Lists.List;
         Cntexmp : in out Cntexample_File_Maps.Map);
      --  Insert pretty printed values Value in a counterexample Cntexmp

      --------------------------------
      -- Accumulate_Expl_For_Entity --
      --------------------------------

      procedure Accumulate_Expl_For_Entity
        (E : Entity_Id; Mode : Modifier; Loop_Id : Entity_Id := Empty) is
      begin
         case Mode is
            when None             =>
               declare
                  Val : constant Value_Access := Find_Binding (E, False);
               begin
                  if Val /= null then
                     Insert_Expl (E, Val.all, Mode);
                  end if;
               end;

            when Old              =>
               declare
                  Val : constant Opt_Value_Type := Find_Old_Value (E);
               begin
                  if Val.Present then
                     Insert_Expl (E, Val.Content, Mode);
                  end if;
               end;

            when Loop_Entry       =>
               declare
                  Val : constant Opt_Value_Type :=
                    Find_Loop_Entry_Value (E, Loop_Id);
               begin
                  if Val.Present then
                     Insert_Expl (E, Val.Content, Mode);
                  end if;
               end;

            when CE_Values.Result =>
               declare
                  Val : constant Value_Access := Find_Binding (E, False);
               begin
                  if Val /= null then
                     Insert_Expl (E, Val.all, Mode);
                  end if;
               end;

            when Index            =>
               null;
         end case;
      end Accumulate_Expl_For_Entity;

      -------------------------
      -- Insert_Cntexmp_Line --
      -------------------------

      procedure Insert_Cntexmp_Line
        (File    : String;
         Line    : Natural;
         Value   : in out Cntexample_Elt_Lists.List;
         Cntexmp : in out Cntexample_File_Maps.Map) is
      begin
         if not Value.Is_Empty then
            declare
               File_Pos : Cntexample_File_Maps.Cursor;
               Line_Pos : Cntexample_Line_Maps.Cursor;
               Inserted : Boolean;
            begin
               Cntexmp.Insert (File, (others => <>), File_Pos, Inserted);
               Cntexmp (File_Pos).Other_Lines.Insert
                 (Line, Value, Line_Pos, Inserted);
               if not Inserted then
                  Cntexmp (File_Pos).Other_Lines (Line_Pos).Splice
                    (Cntexample_Elt_Lists.No_Element, Value);
               end if;
            end;
         end if;
      end Insert_Cntexmp_Line;

      -----------------
      -- Insert_Expl --
      -----------------

      procedure Insert_Expl (E : Entity_Id; V : Value_Type; Mode : Modifier) is
         Position : Entity_To_Extended_Value_Maps.Cursor;
         Inserted : Boolean;

      begin
         if Is_Internal_Entity (E) then
            return;
         end if;

         Expl.Insert (E, (others => null), Position, Inserted);

         declare
            Arr : Extended_Value_Access renames Expl (Position);
         begin
            if Arr (Mode) = null then
               Arr (Mode) := new Value_Type'(V);
            end if;
         end;
      end Insert_Expl;

      procedure Accumulate_All_Expl is new
        Process_Entities_For_One_Liner (Accumulate_Expl_For_Entity);

      Cntexmp : Cntexample_File_Maps.Map;

      --  Start of processing for Get_Environment_One_Liner

   begin
      --  Find the relevant expression and accumulate information about used
      --  objects.

      Accumulate_All_Expl (N, K);

      --  Create a pretty one liner from Expl

      declare
         VC_Loc          : constant Source_Ptr := Sloc (N);
         VC_File         : constant String := File_Name (VC_Loc);
         VC_Line         : constant Natural :=
           Natural (Get_Logical_Line_Number (VC_Loc));
         VC_Cntexmp_Line : Cntexample_Elt_Lists.List;

      begin
         Build_Pretty_Line (Expl, VC_File, VC_Line, VC_Cntexmp_Line);

         if not VC_Cntexmp_Line.Is_Empty then
            declare
               Position : Cntexample_File_Maps.Cursor;
               Inserted : Boolean;
            begin
               Cntexmp.Insert (VC_File, (others => <>), Position, Inserted);
               Cntexmp (Position).VC_Line := VC_Cntexmp_Line;
            end;
         end if;
      end;

      --  Query the input values of the RAC

      declare
         Init_Cntexmp_JSON : Cntexample_Elt_Lists.List;
         Inputs            : Entity_To_Extended_Value_Maps.Map;
         Init_Loc          : constant Source_Ptr := Sloc (Subp);
         Init_File         : constant String := File_Name (Init_Loc);
         Init_Line         : constant Natural :=
           Natural (Get_Logical_Line_Number (Init_Loc));
         Init_Cntexmp_Line : Cntexample_Elt_Lists.List;

      begin
         for Cu in All_Initial_Values.Iterate loop
            declare
               use Node_To_Value;
               Position : Entity_To_Extended_Value_Maps.Cursor;
               Inserted : Boolean;
            begin
               Inputs.Insert (Key (Cu), (others => null), Position, Inserted);

               declare
                  Arr : Extended_Value_Access renames Inputs (Position);
               begin
                  if Arr (None) = null then
                     Arr (None) := new Value_Type'(Element (Cu));
                  end if;
               end;
            end;
         end loop;

         Build_Pretty_Line (Inputs, Init_File, Init_Line, Init_Cntexmp_Line);

         Build_Pretty_Line
           (Inputs,
            Init_File,
            Init_Line,
            Init_Cntexmp_JSON,
            Is_Json_Format => True);

         --  Insert the pretty printed values in a counterexample

         Insert_Cntexmp_Line
           (Init_File, Init_Line, Init_Cntexmp_Line, Cntexmp);

         Input_As_JSON :=
           Json_Formatted_Input'
             (Init_Cntexmp_JSON, To_Unbounded_String (Init_File), Init_Line);
      end;

      --  Query located values of the RAC

      for Cu_Loc in All_Located_Values.Iterate loop
         declare
            use Node_To_Node_To_Value;
            Loc          : constant Source_Ptr := Sloc (Key (Cu_Loc));
            File         : constant String := File_Name (Loc);
            Line         : constant Natural :=
              Natural (Get_Logical_Line_Number (Loc));
            Values       : Entity_To_Extended_Value_Maps.Map;
            Cntexmp_Line : Cntexample_Elt_Lists.List;
            use Node_To_Value;

         begin
            for Cu in Element (Cu_Loc).Iterate loop
               if not Is_Internal_Entity (Key (Cu)) then
                  Values.Insert
                    (Key (Cu),
                     (None => new Value_Type'(Element (Cu)), others => null));
               end if;
            end loop;

            Build_Pretty_Line (Values, File, Line, Cntexmp_Line);

            --  Insert the pretty printed values in a counterexample

            Insert_Cntexmp_Line (File, Line, Cntexmp_Line, Cntexmp);
         end;
      end loop;

      --  Add values of the loop id for all enclosing loops up to the enclosing
      --  unit.

      declare
         function Is_Body_Or_Loop (N : Node_Id) return Boolean
         is (Nkind (N) in N_Loop_Statement | N_Entity_Body);

         function Enclosing_Loop_Stmt is new
           First_Parent_With_Property (Is_Body_Or_Loop);

         P : Node_Id := N;
      begin
         loop
            P := Enclosing_Loop_Stmt (P);
            exit when No (P) or else Nkind (P) /= N_Loop_Statement;
            declare
               Scheme : constant Node_Id := Iteration_Scheme (P);
            begin
               if Present (Scheme) and then No (Condition (Scheme)) then
                  declare
                     Over_Range        : constant Boolean :=
                       Present (Loop_Parameter_Specification (Scheme));
                     Id                : constant Entity_Id :=
                       Get_Quantified_Variable (Scheme, Over_Range);
                     Val               : constant Value_Access :=
                       Find_Binding (Id, False);
                     Loop_Map          : Entity_To_Extended_Value_Maps.Map;
                     Loop_Loc          : constant Source_Ptr := Sloc (P);
                     Loop_File         : constant String :=
                       File_Name (Loop_Loc);
                     Loop_Line         : constant Natural :=
                       Natural (Get_Logical_Line_Number (Loop_Loc));
                     Loop_Cntexmp_Line : Cntexample_Elt_Lists.List;

                  begin
                     if Val /= null and then not Is_Internal_Entity (Id) then
                        Loop_Map.Insert (Id, (None => Val, others => null));
                        Build_Pretty_Line
                          (Loop_Map, Loop_File, Loop_Line, Loop_Cntexmp_Line);
                        Insert_Cntexmp_Line
                          (Loop_File, Loop_Line, Loop_Cntexmp_Line, Cntexmp);
                     end if;
                  end;
               end if;
            end;
         end loop;
      end;

      return Cntexample_Data'(Cntexmp, Input_As_JSON);

   end Get_Environment_CE;

   ----------------------
   -- Is_Ada_File_Name --
   ----------------------

   function Is_Ada_File_Name (File : String) return Boolean is
   begin
      return
        File'Length >= 4
        and then File ((File'Last - 2) .. File'Last) in "adb" | "ads";
   end Is_Ada_File_Name;

   ----------------------
   -- Is_Uninitialized --
   ----------------------

   function Is_Uninitialized
     (Element_Decl : Entity_Id; Element_File : String; Element_Line : Natural)
      return Boolean is
   begin
      --  Counterexample element can be uninitialized only if its location
      --  is the same as location of its declaration (otherwise it has been
      --  assigned or it is a part of construct that triggers VC - and flow
      --  analysis would issue an error in this case).

      if File_Name (Sloc (Element_Decl)) = Element_File
        and then
          Natural (Get_Logical_Line_Number (Sloc (Element_Decl)))
          = Element_Line
      then

         --  Cover cases of uninitialized procedure parameter and uninitialized
         --  variable

         return
           Ekind (Element_Decl) = E_Out_Parameter
           or else
             (Ekind (Element_Decl) = E_Variable
              and then not Is_Quantified_Loop_Param (Element_Decl)
              and then
                Nkind (Enclosing_Declaration (Element_Decl))
                = N_Object_Declaration
              and then No (Expression (Enclosing_Declaration (Element_Decl)))
              and then
                Default_Initialization (Etype (Element_Decl))
                = No_Default_Initialization);

      end if;

      return False;
   end Is_Uninitialized;

   ------------------------------------
   -- Process_Entities_For_One_Liner --
   ------------------------------------

   procedure Process_Entities_For_One_Liner (N : Node_Id; K : VC_Kind) is

      function Process_Node (N : Node_Id) return Atree.Traverse_Result;
      --  Process all relevant values in N

      procedure Process_Basic_Entity (E : Entity_Id);
      --  Insert relevant values for an entity

      procedure Process_Globals (Subp : Entity_Id; Discard_Writes : Boolean);
      --  Process globals of a subprogram. If Discard_Writes is True, do not
      --  consider outputs of the subprogram.

      procedure Process_All (N : Node_Id);
      --  Process all relevant values in N and its children

      --------------------------
      -- Process_Basic_Entity --
      --------------------------

      procedure Process_Basic_Entity (E : Entity_Id) is
      begin
         if Ekind (E)
            in E_Variable | E_Constant | E_Loop_Parameter | Formal_Kind
           and then not Is_Discriminal (E)
           and then not Is_Protected_Component_Or_Discr_Or_Part_Of (E)
         then
            Process_Entity (E, None);

         --  For scalar types, traverse the bounds

         elsif Is_Scalar_Type (E) then
            Process_All (Get_Range (E));

         --  For scalar types, traverse the bounds

         elsif Is_Array_Type (E) then
            declare
               Index : Node_Id := First_Index (E);
            begin
               while Present (Index) loop
                  Process_All (Get_Range (Index));
                  Next_Index (Index);
               end loop;
            end;

         elsif Is_Type (E) and then Has_Discriminants (E) then
            declare
               Elmt : Elmt_Id := First_Elmt (Discriminant_Constraint (E));
            begin
               while Present (Elmt) loop
                  Process_All (Node (Elmt));
                  Next_Elmt (Elmt);
               end loop;
            end;
         end if;
      end Process_Basic_Entity;

      ---------------------
      -- Process_Globals --
      ---------------------

      procedure Process_Globals (Subp : Entity_Id; Discard_Writes : Boolean) is
         Read_Ids  : Flow_Types.Flow_Id_Sets.Set;
         Write_Ids : Flow_Types.Flow_Id_Sets.Set;

      begin
         --  Collect global variables potentially read and written

         Flow_Utility.Get_Proof_Globals
           (Subprogram      => Subp,
            Reads           => Read_Ids,
            Writes          => Write_Ids,
            Erase_Constants => False);

         for V of Read_Ids loop
            if V.Kind = Direct_Mapping then
               Process_Basic_Entity (Get_Direct_Mapping_Id (V));
            end if;
         end loop;

         if not Discard_Writes then
            for V of Write_Ids loop
               if V.Kind = Direct_Mapping then
                  Process_Basic_Entity (Get_Direct_Mapping_Id (V));
               end if;
            end loop;
         end if;
      end Process_Globals;

      ------------------
      -- Process_Node --
      ------------------

      function Process_Node (N : Node_Id) return Atree.Traverse_Result is
      begin
         case Nkind (N) is
            when N_Subprogram_Call              =>

               --  Manually add global reads, as they will not be traversed.
               --  Discard global writes, only preconditions are located at
               --  subprogram calls.

               Process_Globals
                 (Get_Called_Entity_For_Proof (N), Discard_Writes => True);

            when N_Identifier | N_Expanded_Name =>

               --  Add values for referenced objects in Expl

               declare
                  E : constant Entity_Id := SPARK_Atree.Entity (N);
               begin
                  if Present (E) then
                     Process_Basic_Entity (E);
                  end if;
               end;
               return Atree.Skip;

            when N_Attribute_Reference          =>

               --  For 'Old and 'Loop_Entry, print the old value of referenced
               --  variables. Stop the search to avoid pulling useless values.
               --  Do not assume that we necessarily have values for these
               --  references in the map. It might not be the case if parts of
               --  the prefix is not evaluated.

               case Get_Attribute_Id (Attribute_Name (N)) is
                  when Attribute_Old        =>
                     declare
                        Variables : constant Flow_Id_Sets.Set :=
                          Get_Variables_For_Proof (Prefix (N), Prefix (N));
                        Var       : Entity_Id;
                     begin
                        for V of Variables loop
                           if V.Kind = Direct_Mapping then
                              Var := Get_Direct_Mapping_Id (V);
                              Process_Entity (Var, Old);
                           end if;
                        end loop;
                     end;
                     return Atree.Skip;

                  when Attribute_Loop_Entry =>
                     declare
                        Variables : constant Flow_Id_Sets.Set :=
                          Get_Variables_For_Proof (Prefix (N), Prefix (N));
                        Loop_Id   : constant Entity_Id :=
                          Name_For_Loop_Entry (N);
                        Var       : Entity_Id;
                     begin
                        for V of Variables loop
                           if V.Kind = Direct_Mapping then
                              Var := Get_Direct_Mapping_Id (V);
                              Process_Entity (Var, Loop_Entry, Loop_Id);
                           end if;
                        end loop;
                     end;
                     return Atree.Skip;

                  when Attribute_Result     =>
                     declare
                        E : constant Entity_Id :=
                          SPARK_Atree.Entity (Prefix (N));
                     begin
                        Process_Entity (E, CE_Values.Result);
                     end;
                     return Atree.Skip;

                  when others               =>
                     null;
               end case;

            when N_Target_Name                  =>
               declare
                  function Is_Assignment (N : Node_Id) return Boolean
                  is (Nkind (N) = N_Assignment_Statement);
                  function Find_Assignment is new
                    First_Parent_With_Property (Is_Assignment);
                  Assign : constant Node_Id := Find_Assignment (N);
               begin
                  Process_All (Name (Assign));
               end;

            when others                         =>
               null;
         end case;
         return Atree.OK;
      end Process_Node;

      procedure Process_All_Internal is new Traverse_More_Proc (Process_Node);

      procedure Process_All (N : Node_Id) renames Process_All_Internal;
   begin
      --  Find the relevant expression and call Process_Entity on used objects

      case Nkind (N) is
         when N_Defining_Identifier   =>

            --  Some checks are located on subprogram entities.
            --  Get all inputs and outputs of the subprogram.

            if Ekind (N) in Subprogram_Kind | Entry_Kind then
               declare
                  F : Entity_Id := First_Formal (N);
               begin
                  while Present (F) loop
                     Process_Basic_Entity (F);
                     Next_Formal (F);
                  end loop;
               end;
               Process_Globals (N, Discard_Writes => False);
               if Ekind (N) = E_Function then
                  Process_Entity (N, CE_Values.Result);
               end if;
            else
               Process_Basic_Entity (N);
            end if;

         when N_Subexpr               =>

            --  For index checks, we want to include the array object to get
            --  the bounds.

            if K = VC_Index_Check
              and then Nkind (Atree.Parent (N)) = N_Indexed_Component
              and then
                not Is_Static_Array_Type (Etype (Prefix (Atree.Parent (N))))
            then
               Process_All (N);
               Process_All (Prefix (Atree.Parent (N)));

            --  Discriminant checks might occur in delta aggregates. Include
            --  the expression.

            elsif K = VC_Discriminant_Check
              and then Nkind (N) in N_Identifier | N_Expanded_Name
              and then Ekind (Entity (N)) = E_Component
              and then Nkind (Atree.Parent (N)) = N_Component_Association
            then
               Process_All (N);
               declare
                  use Namet;
                  P : constant Node_Id := Atree.Parent (Atree.Parent (N));
               begin
                  if Nkind (P) = N_Delta_Aggregate then
                     Process_All (Expression (P));
                  elsif Nkind (Atree.Parent (P)) = N_Attribute_Reference
                    and then Attribute_Name (Atree.Parent (P)) = Name_Update
                  then
                     Process_All (Prefix (Atree.Parent (P)));
                  end if;
               end;

            --  For division checks, we only consider the right operand

            elsif K = VC_Division_Check and then Nkind (N) in N_Binary_Op then
               Process_All (Right_Opnd (N));

            --  For scalar range checks, include the bounds

            elsif K = VC_Range_Check and then Is_Scalar_Type (Etype (N)) then
               Process_Basic_Entity (Etype (N));
               Process_All (N);

            --  For discriminant and length checks try to find the type we are
            --  converting to. Process its constraints.

            elsif K in VC_Discriminant_Check | VC_Length_Check then
               declare
                  Par    : constant Node_Id := Atree.Parent (N);
                  Exp_Ty : Entity_Id := Empty;
               begin
                  case Nkind (Atree.Parent (N)) is
                     when N_Assignment_Statement =>
                        Exp_Ty := Etype (Name (Par));

                     when N_Object_Declaration   =>
                        Exp_Ty := Etype (Defining_Identifier (Par));

                     when N_Type_Conversion
                        | N_Unchecked_Type_Conversion
                        | N_Qualified_Expression =>
                        Exp_Ty := Etype (Par);

                     when others                 =>
                        null;
                  end case;

                  if Present (Exp_Ty) and then Is_Constrained (Exp_Ty) then
                     Process_Basic_Entity (Exp_Ty);
                  end if;
               end;

               Process_All (N);
            else
               Process_All (N);
            end if;

            --  Force the value of all quantified variables and declared above
            --  expressions above N.

            declare
               P : Node_Id := N;
            begin
               loop
                  P := Atree.Parent (P);
                  exit when Nkind (P) not in N_Subexpr;
                  if Nkind (P) = N_Quantified_Expression then
                     declare
                        Over_Range : constant Boolean :=
                          Present (Loop_Parameter_Specification (P));
                        Id         : constant Entity_Id :=
                          Get_Quantified_Variable (P, Over_Range);
                        Expr       : constant Node_Id :=
                          Get_Expr_Quantified_Over (P, Over_Range);
                     begin
                        Process_All (Expr);
                        Process_Basic_Entity (Id);

                        --  Also add the potential additional index used for
                        --  for of quantifications in Why.

                        Process_Entity (Id, Index);
                     end;
                  elsif Nkind (P) = N_Expression_With_Actions then
                     declare
                        Action : Node_Id := First (Actions (P));
                     begin
                        while Present (Action) loop
                           if Nkind (Action) = N_Object_Declaration then
                              Process_All (Expression (Action));
                           end if;
                           Next (Action);
                        end loop;
                     end;
                  end if;
               end loop;
            end;

         when N_Pragma                =>

            --  Disjointness or completeness of Contract_Cases

            if Get_Pragma_Id (N) = Pragma_Contract_Cases then
               declare
                  Aggr          : constant Node_Id :=
                    Expression (First (Pragma_Argument_Associations (N)));
                  Contract_Case : Node_Id :=
                    First (Component_Associations (Aggr));
               begin
                  while Present (Contract_Case) loop
                     Process_All (First (Choice_List (Contract_Case)));
                     Next (Contract_Case);
                  end loop;
               end;
            end if;

         when N_Assignment_Statement  =>
            Process_All (Expression (N));

            --  Add the left-hand side for discriminant checks

            if K = VC_Discriminant_Check then
               Process_All (SPARK_Atree.Name (N));
            end if;

         when N_Component_Association =>
            Process_All (Expression (N));

            --  On contract cases, the choices shall be evaluated in the pre
            --  state.

            if K = VC_Contract_Case then
               if not Is_Others_Choice (Choice_List (N)) then
                  declare
                     C : Node_Id := First (Choice_List (N));
                  begin
                     loop
                        declare
                           Variables : constant Flow_Id_Sets.Set :=
                             Get_Variables_For_Proof (C, N);
                           Var       : Entity_Id;
                        begin
                           for V of Variables loop
                              if V.Kind = Direct_Mapping then
                                 Var := Get_Direct_Mapping_Id (V);
                                 Process_Entity (Var, Old);
                              end if;
                           end loop;
                        end;
                        Next (C);
                        exit when No (C);
                     end loop;
                  end;
               end if;
            end if;

         when others                  =>
            null;
      end case;
   end Process_Entities_For_One_Liner;

   -----------------------------
   -- Reconstruct_Index_Value --
   -----------------------------

   function Reconstruct_Index_Value
     (Value : Unbounded_String; Quant_Id : Entity_Id) return Unbounded_String
   is
      function Refine_Container_Iterator_Value
        (R_Value        : Unbounded_String;
         Cont_Typ       : Entity_Id;
         Container_Name : Unbounded_String) return Unbounded_String;
      --  Refine value for iterator over types with the Iterable aspect. For
      --  example, for a type:
      --
      --  type T is private with
      --    Iterable => (First       => My_First,
      --                 Has_Element => My_Has_Element,
      --                 Next        => My_Next,
      --                 Element     => My_Element);
      --
      --  It will return My_Element (Container_Name, <value>).
      --  If the type has an Iterable_For_Proof of a model kind, it will be
      --  taken into account, for example, if we add:
      --
      --  type T2 is private with
      --    Iterable => (First       => My_First_2,
      --                 Has_Element => My_Has_Element_2,
      --                 Next        => My_Next_2,
      --                 Element     => My_Element_2);
      --
      --  function Model (X : T) return T2;
      --  pragma Annotate (GNATprove, Iterable_For_Proof, "Model", Model);
      --
      --  then for of iterators on T will refined against T2's cursor type and
      --  then printed as My_Element_2 (Model (Container_Name), <value>).

      -------------------------------------
      -- Refine_Container_Iterator_Value --
      -------------------------------------

      function Refine_Container_Iterator_Value
        (R_Value        : Unbounded_String;
         Cont_Typ       : Entity_Id;
         Container_Name : Unbounded_String) return Unbounded_String
      is
         Found         : Boolean;
         Iterable_Info : Iterable_Annotation;

      begin
         --  Construct the expression to be used for the container name

         Retrieve_Iterable_Annotation (Cont_Typ, Found, Iterable_Info);

         if Found then

            --  Iterable annotation should be a Model annotation. Indeed, if a
            --  Contains iterable annotation is provided, no temporary
            --  should be introduced for "for of" quantification.

            pragma
              Assert (Iterable_Info.Kind = SPARK_Definition.Annotate.Model);

            --  Prepend the name of the Model function to the container name

            return
              Refine_Container_Iterator_Value
                (R_Value,
                 Etype (Iterable_Info.Entity),
                 Raw_Source_Name (Iterable_Info.Entity)
                 & " ("
                 & Container_Name
                 & ")");
         else

            --  We have found the ultimate model type

            return
              Raw_Source_Name
                (Get_Iterable_Type_Primitive (Cont_Typ, Name_Element))
              & " ("
              & Container_Name
              & ", "
              & R_Value
              & ")";
         end if;
      end Refine_Container_Iterator_Value;

      function Is_Quantified_Expr (N : Node_Id) return Boolean
      is (Nkind (N) = N_Quantified_Expression);
      function Enclosing_Quantified_Expr is new
        First_Parent_With_Property (Is_Quantified_Expr);

      Container : constant Entity_Id :=
        Get_Container_In_Iterator_Specification
          (Iterator_Specification (Enclosing_Quantified_Expr (Quant_Id)));
      pragma Assert (Present (Container));

      Container_Typ : constant Entity_Id := Retysp (Etype (Container));

   begin
      --  E = A (<value>)

      if Is_Array_Type (Container_Typ) then
         return Raw_Source_Name (Container) & " (" & Value & ")";

      --  E = Element (C, <value>)

      else
         return
           Refine_Container_Iterator_Value
             (Value,
              Container_Typ,
              To_Unbounded_String (Raw_Source_Name (Container)));
      end if;
   end Reconstruct_Index_Value;

   --------------------------------
   -- Remove_Irrelevant_Branches --
   --------------------------------

   --  This is the main function of a feature which records a boolean
   --  counterexample value for any branching condition done in the code (if
   --  and case). These counterexamples are tagged with a specific attribute
   --  "branch_id:number" (with number being the node_id of the if/case).
   --  In this context, this function first search for the node_id labels of
   --  counterexamples and then removes the lines that do not corresponds to
   --  the branch taken by the counterexample in the if/case (using the value
   --  of the CE).

   function Remove_Irrelevant_Branches
     (Cntexmp : Cntexample_File_Maps.Map) return Cntexample_File_Maps.Map
   is

      package Supp_Lines is new CE_Interval_Sets (N => Physical_Line_Number);

      function Get_Interval_Case
        (N : Node_Id; B : Boolean) return Supp_Lines.Interval_Set
      with Pre => Nkind (N) = N_Case_Statement_Alternative;
      --  The case statement are translated to new ifs in Why3 so we can
      --  eliminate case by case (the order of branches is kept):
      --  * a branch is taken: we can remove all the subsequent "when"
      --    statements (they are not taken). We *cannot* remove branches
      --    * before * this one as, if an earlier branch was taken the model
      --    is still correct if the current one is also taken (making it
      --    inconsistent).
      --  * a branch is not taken: we can remove it as we are sure it is not
      --    taken

      function Get_Interval_For_Branch (N : Node_Id) return Supp_Lines.Interval
      with Pre => Nkind (N) in N_If_Statement | N_Elsif_Part;

      function Get_Interval_For_Branch_Case
        (N : Node_Id) return Supp_Lines.Interval
      with Pre => Nkind (N) = N_Case_Statement_Alternative;

      function Get_Interval_If
        (N : Node_Id; B : Boolean) return Supp_Lines.Interval_Set
      with Pre => Nkind (N) in N_If_Statement | N_Elsif_Part;

      function Get_P (E : Entity_Id) return Physical_Line_Number
      is (Get_Physical_Line_Number (Sloc (E)));
      --  Abbreviation for querying the first line of an entity

      procedure Search_Labels
        (S : in out Supp_Lines.Interval_Set;
         L : String_Lists.List;
         V : Cntexmp_Value_Ptr);
      --  This procedure fills S with new values corresponding to branches that
      --  should not be taken for display of counterexamples.

      -----------------------
      -- Get_Interval_Case --
      -----------------------

      function Get_Interval_Case
        (N : Node_Id; B : Boolean) return Supp_Lines.Interval_Set
      is
         S : Supp_Lines.Interval_Set := Supp_Lines.Create;
      begin
         if not B then
            --  This branch is not taken, remove it

            Supp_Lines.Insert (S, Get_Interval_For_Branch_Case (N));
            return S;

         else
            --  This branch is taken, removes all branches *after* it. If one
            --  is taken before, the result is random because it is a part of
            --  a logic expression that is never used -> nothing more can be
            --  deduced.

            if Present (Next (N)) then
               Supp_Lines.Insert
                 (S,
                  (L_Bound => Get_P (Next (N)),
                   R_Bound =>
                     Get_Physical_Line_Number
                       (End_Location (Enclosing_Statement (N)))));
            end if;

         end if;
         return S;
      end Get_Interval_Case;

      -----------------------------
      -- Get_Interval_For_Branch --
      -----------------------------

      function Get_Interval_For_Branch (N : Node_Id) return Supp_Lines.Interval
      is
      begin
         if Nkind (N) = N_If_Statement then
            declare
               Lbound : constant Physical_Line_Number :=
                 Get_P (Nlists.First (Then_Statements (N)));
               Rbound : constant Physical_Line_Number :=
                 (if Present (Elsif_Parts (N))
                  then Get_P (First (Elsif_Parts (N))) - 1

                  elsif Present (Else_Statements (N))
                  then Get_P (First (Else_Statements (N))) - 1

                  else Get_Physical_Line_Number (End_Location (N)));

            begin
               return
                 (L_Bound => Lbound,
                  R_Bound => Physical_Line_Number'Max (Lbound, Rbound));
            end;

         elsif Nkind (N) = N_Elsif_Part then
            declare
               Lbound : constant Physical_Line_Number :=
                 Get_P (First (Then_Statements (N)));
               Rbound : constant Physical_Line_Number :=
                 (if Present (Next (N))
                  then Get_P (Next (N)) - 1
                  else
                    (if Present (Else_Statements (Enclosing_Statement (N)))
                     then
                       Get_P
                         (First (Else_Statements (Enclosing_Statement (N))))
                     else
                       Get_Physical_Line_Number
                         (End_Location (Enclosing_Statement (N)))));

            begin
               return
                 (L_Bound => Get_P (First (Then_Statements (N))),
                  R_Bound => Physical_Line_Number'Max (Lbound, Rbound));
            end;

         else

            --  Cannot be accessed (precondition)
            raise Program_Error;
         end if;
      end Get_Interval_For_Branch;

      ----------------------------------
      -- Get_Interval_For_Branch_Case --
      ----------------------------------

      function Get_Interval_For_Branch_Case
        (N : Node_Id) return Supp_Lines.Interval is
      begin
         if Present (Next (N)) then
            return
              (L_Bound => Get_P (N),
               R_Bound => Physical_Line_Number'Max (1, Get_P (Next (N)) - 1));
         else
            return
              (L_Bound => Get_P (N),
               R_Bound =>
                 Physical_Line_Number
                   (End_Location (Enclosing_Statement (N))));
         end if;

      end Get_Interval_For_Branch_Case;

      ---------------------
      -- Get_Interval_If --
      ---------------------

      --  The elsif statement are translated to new ifs in Why3 so we can
      --  eliminate branch by branch (the order of branches is kept):
      --  * a branch is taken: we can remove all the subsequent elsif/else
      --    statements (they are not taken). We *cannot* remove branches
      --    * before * this one as, if an earlier branch was taken the model
      --    is still correct if the current one is also taken (making it
      --    inconsistent).
      --  * a branch is not taken: we can remove it as we are sure it is not
      --    taken

      function Get_Interval_If
        (N : Node_Id; B : Boolean) return Supp_Lines.Interval_Set
      is
         S : Supp_Lines.Interval_Set := Supp_Lines.Create;
      begin
         if not B then
            --  This branch is not taken: remove it.

            Supp_Lines.Insert (S, Get_Interval_For_Branch (N));
            return S;

         else
            --  This branch is taken, removes all branches *after* it. If one
            --  is taken before, the result is random because it is a part of
            --  a logic expression that is never used -> nothing more can be
            --  deduced.

            if Nkind (N) = N_If_Statement then
               if Present (Elsif_Parts (N)) then
                  Supp_Lines.Insert
                    (S,
                     (L_Bound => Get_P (First (Elsif_Parts (N))),
                      R_Bound => Get_Physical_Line_Number (End_Location (N))));

               elsif Present (Else_Statements (N)) then
                  Supp_Lines.Insert
                    (S,
                     (L_Bound => Get_P (First (Else_Statements (N))),
                      R_Bound => Get_Physical_Line_Number (End_Location (N))));
               else

                  --  No elsif or else branch so we don't need to remove
                  --  anything
                  null;
               end if;

            elsif Nkind (N) = N_Elsif_Part then

               if Present (Next (N)) then
                  Supp_Lines.Insert
                    (S,
                     (L_Bound => Get_P (Next (N)),
                      R_Bound =>
                        Get_Physical_Line_Number
                          (End_Location (Enclosing_Statement (N)))));

               else

                  --  If there is no else statements and no following elsif we
                  --  do nothing.

                  if Present (Else_Statements (Enclosing_Statement (N))) then
                     Supp_Lines.Insert
                       (S,
                        (L_Bound =>
                           Get_P
                             (First
                                (Else_Statements (Enclosing_Statement (N)))),
                         R_Bound =>
                           Get_Physical_Line_Number
                             (End_Location (Enclosing_Statement (N)))));
                  end if;
               end if;

            else
               raise Constraint_Error;
            end if;

            return S;
         end if;
      end Get_Interval_If;

      -------------------
      -- Search_Labels --
      -------------------

      procedure Search_Labels
        (S : in out Supp_Lines.Interval_Set;
         L : String_Lists.List;
         V : Cntexmp_Value_Ptr) is
      begin
         for Elt of L loop
            if Elt'Length > 10
              and then Elt (Elt'First .. Elt'First + 9) = "branch_id="
            then

               declare
                  N : constant Node_Id :=
                    Get_Entity_Id (False, Elt (Elt'First + 10 .. Elt'Last));
               begin
                  if Present (N) and V.T = Cnt_Boolean then

                     if Nkind (N) in N_If_Statement | N_Elsif_Part then
                        Supp_Lines.Insert_Union (S, Get_Interval_If (N, V.Bo));

                     elsif Nkind (N) = N_Case_Statement_Alternative then
                        Supp_Lines.Insert_Union
                          (S, Get_Interval_Case (N, V.Bo));

                     else
                        null;
                     end if;
                  end if;
               end;
            end if;
         end loop;

      end Search_Labels;

      --  Start of processing for Remove_Irrelevant_Branches

      Remapped_Cntexmp : Cntexample_File_Maps.Map := Cntexmp;
      --  Temporary variable containing the branch to remove in files
      Suppressed_Lines : Supp_Lines.Interval_Set := Supp_Lines.Create;
   begin
      --  VC_Line is already empty at this point

      for Files of Remapped_Cntexmp loop
         Supp_Lines.Clear (Suppressed_Lines);

         --  Collect node_ids that remove lines in Suppressed_Lines
         for Lines of Files.Other_Lines loop
            for Elt of Lines loop
               Search_Labels (Suppressed_Lines, Elt.Labels, Elt.Value);
            end loop;
         end loop;

         declare
            Cnt_Line_Map : Cntexample_Line_Maps.Map :=
              Cntexample_Line_Maps.Empty_Map;
         begin

            --  remove lines according to suppressed_lines collected
            for Cursor in Files.Other_Lines.Iterate loop
               declare
                  Line : constant Natural := Cntexample_Line_Maps.Key (Cursor);
               begin

                  if not Supp_Lines.Has_Containing_Interval
                           (Suppressed_Lines, Physical_Line_Number (Line))
                  then
                     Cntexample_Line_Maps.Insert
                       (Cnt_Line_Map,
                        Line,
                        Cntexample_Line_Maps.Element (Cursor));
                  end if;
               end;
            end loop;
            Files.Other_Lines := Cnt_Line_Map;
         end;
      end loop;

      return Remapped_Cntexmp;
   end Remove_Irrelevant_Branches;

   -------------------
   -- Remap_VC_Info --
   -------------------

   function Remap_VC_Info
     (Cntexmp : Cntexample_File_Maps.Map; VC_File : String; VC_Line : Natural)
      return Cntexample_File_Maps.Map
   is
      Remapped_Cntexmp : Cntexample_File_Maps.Map := Cntexmp;

      C        : Cntexample_File_Maps.Cursor;
      Inserted : Boolean;
      VC       : Cntexample_Elt_Lists.List;

   begin
      --  Search for VC_Line (there is only one). It can be in any file,
      --  depending on the location used by Why3 (when checking that a
      --  predicate holds, it sometimes uses the location of the predicate
      --  instead of the location where it is called).

      for Elt of Remapped_Cntexmp loop
         if not Elt.VC_Line.Is_Empty then
            pragma Assert (VC.Is_Empty);
            VC := Elt.VC_Line;
            Elt.VC_Line.Clear;
         end if;
      end loop;

      if VC.Is_Empty then
         return Remapped_Cntexmp;
      end if;

      --  Insert it at the appropriate location in Remapped_Cntexmp, possibly
      --  deleting other information in the process.

      Remapped_Cntexmp.Insert
        (Key      => VC_File,
         New_Item =>
           (Other_Lines    => Cntexample_Line_Maps.Empty_Map,
            VC_Line        => Cntexample_Elt_Lists.Empty_List,
            Previous_Lines => Previous_Line_Maps.Empty_Map),
         Position => C,
         Inserted => Inserted);

      Remapped_Cntexmp (C).Other_Lines.Include (VC_Line, VC);

      return Remapped_Cntexmp;
   end Remap_VC_Info;

   function Remap_VC_Info
     (Cntexmp : Cntexample_File_Maps.Map; VC_Loc : Source_Ptr)
      return Cntexample_File_Maps.Map
   is
      File : constant String := File_Name (VC_Loc);
      Line : constant Logical_Line_Number := Get_Logical_Line_Number (VC_Loc);
   begin
      return Remap_VC_Info (Cntexmp, File, Integer (Line));
   end Remap_VC_Info;

end CE_Display;
