------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              G N A T 2 W H Y _ C O U N T E R _ E X A M P L E S           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2016-2022, AdaCore                     --
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
with Ada.Strings;                 use Ada.Strings;
with Ada.Strings.Unbounded;       use Ada.Strings.Unbounded;
with CE_Interval_Sets;
with CE_Parsing;                  use CE_Parsing;
with CE_Pretty_Printing;          use CE_Pretty_Printing;
with CE_Utils;                    use CE_Utils;
with CE_Values;                   use CE_Values;
with Erroutc;                     use Erroutc;
with Flow_Utility.Initialization; use Flow_Utility.Initialization;
with Gnat2Why_Args;
with Gnat2Why_Opts;               use Gnat2Why_Opts;
with Gnat2Why.Util;               use Gnat2Why.Util;
with Nlists;                      use Nlists;
with Sinput;                      use Sinput;
with Snames;                      use Snames;
with SPARK_Atree;                 use SPARK_Atree;
with SPARK_Atree.Entities;        use SPARK_Atree.Entities;
with SPARK_Definition;            use SPARK_Definition;
with SPARK_Definition.Annotate;   use SPARK_Definition.Annotate;
with SPARK_Util;                  use SPARK_Util;
with SPARK_Util.Types;            use SPARK_Util.Types;

package body CE_Display is

   function Remap_VC_Info
     (Cntexmp : Cntexample_File_Maps.Map;
      VC_File : String;
      VC_Line : Natural)
      return Cntexample_File_Maps.Map;
   --  Map counterexample information related to the current VC to the
   --  location of the check in the Ada file.
   --  In Cntexmp, this information is mapped to the field "vc_line" of the
   --  JSON object representing the file where the construct is located.

   function Remove_Irrelevant_Branches
     (Cntexmp : Cntexample_File_Maps.Map)
      return Cntexample_File_Maps.Map;
   --  Remove counterexample branches that are not taken

   function Is_Ada_File_Name (File : String) return Boolean;
   --  check if the filename is an Ada
   --  ??? This check is wrong, need to get rid of it

   function Is_Uninitialized
     (Element_Decl : Entity_Id;
      Element_File : String;
      Element_Line : Natural)
      return Boolean
   with Pre => Nkind (Element_Decl) in N_Entity;
   --  Return True if the counterexample element with given declaration at
   --  given position is uninitialized.

   function Compare_Name (X, Y : Entity_Id) return Boolean is
     (Source_Name (X) < Source_Name (Y)
      or else (Source_Name (X) = Source_Name (Y) and then X < Y));
   --  Variables are stored in alphabetical order. Compare the entity id in
   --  case there are homonyms.

   package Name_Ordered_Entities_Sets is
     new Ada.Containers.Ordered_Sets
       (Element_Type => Entity_Id,
        "<"          => Compare_Name);

   procedure Build_Pretty_Line
     (Variables               : Entity_To_Extended_Value_Maps.Map;
      File                    : String;
      Line                    : Natural;
      Pretty_Line_Cntexmp_Arr : out Cntexample_Elt_Lists.List);
   --  Build pretty printed JSON array of counterexample elements.
   --  @Variables stores information about values and fields of
   --    variables at a single source code location (line).

   function Reconstruct_Index_Value
     (Value    : Unbounded_String;
      Quant_Id : Entity_Id) return Unbounded_String;
   --  Reconstruct a string for the value of the Ada quantified variable
   --  in a FOR OF quantification from the value for the Why3 quantified
   --  variable.

   -----------------------
   -- Build_Pretty_Line --
   -----------------------

   procedure Build_Pretty_Line
     (Variables               : Entity_To_Extended_Value_Maps.Map;
      File                    : String;
      Line                    : Natural;
      Pretty_Line_Cntexmp_Arr : out Cntexample_Elt_Lists.List)
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
            Var_Name : constant String := Source_Name (Var);
            Value    : Value_Type;
            Name     : Unbounded_String;
         begin
            for Var_Mod in Modifier loop
               Name := To_Unbounded_String (Var_Name);

               --  Update the name with the modifier

               case Var_Mod is
                  when None | Index =>
                     null;
                  when Old =>
                     Append (Name, "'Old");
                  when Loop_Entry =>
                     Append (Name, "'Loop_Entry");
                  when Result =>
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
                           Pretty_Value.Str :=
                             Reconstruct_Index_Value (Pretty_Value.Str, Var);
                        end if;

                        Pretty_Line_Cntexmp_Arr.Append
                          (Cntexample_Elt'(K       => Pretty_Printed,
                                           Kind    => CEE_Variable,
                                           Name    => Name,
                                           Val_Str => Pretty_Value));
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
                       (Name, Value, Pretty_Line_Cntexmp_Arr);
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
      VC_Loc  : Source_Ptr)
      return Cntexample_File_Maps.Map
   is
      use Cntexample_File_Maps;

      procedure Create_Pretty_Line
        (Pretty_File_Cntexmp : in out Cntexample_Lines;
         File                : String;
         Line                : Natural;
         Line_Cntexmp        : Cntexample_Elt_Lists.List;
         Is_Previous         : Boolean;
         LI_Node             : Node_Id);
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
         LI_Node             : Node_Id)
      is
         Variables               : Entity_To_Extended_Value_Maps.Map;
         Pretty_Line_Cntexmp_Arr : Cntexample_Elt_Lists.List;

      --  Start of processing for Create_Pretty_Line

      begin
         Parse_Counterexample_Line (Line_Cntexmp, Variables);

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
                    (Line, (Line_Cnt => Pretty_Line_Cntexmp_Arr,
                            Ada_Node => Integer (LI_Node)));
               else
                  Pretty_File_Cntexmp.Other_Lines.Include
                    (Line, Pretty_Line_Cntexmp_Arr);
               end if;
            end if;
         end if;
      end Create_Pretty_Line;

      --  Local variables

      File : constant String := File_Name (VC_Loc);
      Line : constant Logical_Line_Number :=
        Get_Logical_Line_Number (VC_Loc);
      Remapped_Cntexmp : constant Cntexample_File_Maps.Map :=
        Remove_Irrelevant_Branches
          (Remap_VC_Info (Cntexmp, File, Natural (Line)));
      Pretty_Cntexmp : Cntexample_File_Maps.Map :=
        Cntexample_File_Maps.Empty_Map;

   --  Start of processing for Create_Pretty_Cntexmp

   begin
      for File_C in Remapped_Cntexmp.Iterate loop
         declare
            Is_Previous         : Boolean;
            LI_Node             : Node_Id := Types.Empty;
            Filename            : constant String :=
              Compute_Filename_Previous (Key (File_C), Is_Previous, LI_Node);
            Pretty_File_Cntexmp : Cntexample_Lines :=
              (if No_Element /= Pretty_Cntexmp.Find (Filename) then
                  Element (Pretty_Cntexmp.Find (Filename))
               else
                  Cntexample_Lines'(VC_Line        =>
                                      Cntexample_Elt_Lists.Empty_List,
                                    Other_Lines    =>
                                      Cntexample_Line_Maps.Empty_Map,
                                    Previous_Lines =>
                                      Previous_Line_Maps.Empty_Map));
            Lines_Map           : Cntexample_Line_Maps.Map renames
              Element (File_C).Other_Lines;

         begin
            for Line_C in Lines_Map.Iterate loop
               Create_Pretty_Line
                 (Pretty_File_Cntexmp,
                  Filename,
                  Cntexample_Line_Maps.Key (Line_C),
                  Lines_Map (Line_C),
                  Is_Previous,
                  LI_Node);
            end loop;

            --  At this point, the information of VC_line is now in the
            --  Other_Lines field because Remap_VC_Info was applied.
            if Is_Ada_File_Name (Filename) and then
              (not Cntexample_Line_Maps.Is_Empty
                (Pretty_File_Cntexmp.Other_Lines)
              or else
                not Previous_Line_Maps.Is_Empty
                (Pretty_File_Cntexmp.Previous_Lines))
            then
               Pretty_Cntexmp.Include (Filename, Pretty_File_Cntexmp);
            end if;
         end;
      end loop;

      Remove_Vars.Remove_Extra_Vars (Pretty_Cntexmp);

      return Pretty_Cntexmp;

   end Create_Pretty_Cntexmp;

   ---------------------------
   -- Get_Cntexmp_One_Liner --
   ---------------------------

   function Get_Cntexmp_One_Liner
     (Cntexmp : Cntexample_File_Maps.Map;
      VC_Loc  : Source_Ptr)
      return String
   is
      function Get_Cntexmp_Line_Str
        (Cntexmp_Line : Cntexample_Elt_Lists.List) return String;

      --------------------------
      -- Get_Cntexmp_Line_Str --
      --------------------------

      function Get_Cntexmp_Line_Str
        (Cntexmp_Line : Cntexample_Elt_Lists.List) return String
      is
         procedure Before_Next_Element (Str : in out Unbounded_String);
         --  Action on Str before printing the next element

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

         --  Local variables

         Cntexmp_Line_Str : Unbounded_String;

      --  Start of processing for Get_Cntexmp_Line_Str

      begin
         for Elt of Cntexmp_Line loop
            if Elt.Kind /= CEE_Error_Msg then
               declare
                  Num_Elems : Natural := Elt.Val_Str.Count;
                  Cur_Elems : S_String_List.Cursor := Elt.Val_Str.Elems.First;

                  --  Maximum number of elements to print for a single
                  --  variable, whose value can be set arbitrarily. It should
                  --  be small enough that even with multiple variables being
                  --  printed, the output remains small enough that (1) it can
                  --  be output by Errout without truncation, and (2) it is not
                  --  so long as to be confusing to users.
                  Max_Elems : constant := 5;

                  use S_String_List;
               begin
                  --  If the normal display of counterexample values
                  --  would include more than Max_Elems for this variable,
                  --  then display at most Max_Elems values of individual
                  --  subcomponents of the variable. In such a case, simply
                  --  prepend Elt.Name to the string in Cur_Elems, as Cur_Elems
                  --  already contains the rest of the path to the subcomponent
                  --  if any, the equality symbol and the value.

                  if Num_Elems > Max_Elems then
                     Num_Elems := Max_Elems;
                     while Num_Elems > 0
                       and then Has_Element (Cur_Elems)
                     loop
                        Before_Next_Element (Cntexmp_Line_Str);
                        Append (Cntexmp_Line_Str, Elt.Name);
                        Append (Cntexmp_Line_Str, Element (Cur_Elems));
                        Num_Elems := Num_Elems - 1;
                        Next (Cur_Elems);
                     end loop;

                  else
                     Before_Next_Element (Cntexmp_Line_Str);
                     Append (Cntexmp_Line_Str, Elt.Name);
                     Append (Cntexmp_Line_Str, " = ");
                     Append (Cntexmp_Line_Str, Elt.Val_Str.Str);
                  end if;
               end;
            end if;
         end loop;
         return To_String (Cntexmp_Line_Str);
      end Get_Cntexmp_Line_Str;

      File : constant String := File_Name (VC_Loc);
      Line : constant Logical_Line_Number := Get_Logical_Line_Number (VC_Loc);
      File_Cur : constant Cntexample_File_Maps.Cursor := Cntexmp.Find (File);
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

   ----------------------
   -- Is_Ada_File_Name --
   ----------------------

   function Is_Ada_File_Name (File : String) return Boolean is
   begin
      return
        File'Length >= 4 and then
        (File ((File'Last - 2) .. File'Last) in "adb" | "ads");
   end Is_Ada_File_Name;

   ----------------------
   -- Is_Uninitialized --
   ----------------------

   function Is_Uninitialized
     (Element_Decl : Entity_Id;
      Element_File : String;
      Element_Line : Natural)
      return Boolean
   is
   begin
      --  Counterexample element can be uninitialized only if its location
      --  is the same as location of its declaration (otherwise it has been
      --  assigned or it is a part of construct that triggers VC - and flow
      --  analysis would issue an error in this case).

      if File_Name (Sloc (Element_Decl)) = Element_File
        and then
          Natural
            (Get_Logical_Line_Number (Sloc (Element_Decl))) = Element_Line
      then

         --  Uninitialized procedure parameter

         return Ekind (Element_Decl) = E_Out_Parameter

         --  Uninitialized variable

           or else (Ekind (Element_Decl) = E_Variable
                    and then not Is_Quantified_Loop_Param (Element_Decl)
                    and then Nkind (Enclosing_Declaration (Element_Decl)) =
                      N_Object_Declaration
                    and then
                    No (Expression (Enclosing_Declaration (Element_Decl)))
                    and then
                    Default_Initialization
                      (Etype (Element_Decl)) = No_Default_Initialization);

      end if;

      return False;
   end Is_Uninitialized;

   -----------------------------
   -- Reconstruct_Index_Value --
   -----------------------------

   function Reconstruct_Index_Value
     (Value    : Unbounded_String;
      Quant_Id : Entity_Id) return Unbounded_String
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

            pragma Assert
              (Iterable_Info.Kind = SPARK_Definition.Annotate.Model);

            --  Prepend the name of the Model function to the container name

            return Refine_Container_Iterator_Value
              (R_Value,
               Etype (Iterable_Info.Entity),
               Source_Name (Iterable_Info.Entity)
               & " (" & Container_Name & ")");
         else

            --  We have found the ultimate model type

            return Source_Name
              (Get_Iterable_Type_Primitive (Cont_Typ, Name_Element))
              & " (" & Container_Name & ", " & R_Value & ")";
         end if;
      end Refine_Container_Iterator_Value;

      function Is_Quantified_Expr (N : Node_Id) return Boolean is
        (Nkind (N) = N_Quantified_Expression);
      function Enclosing_Quantified_Expr is new
        First_Parent_With_Property (Is_Quantified_Expr);

      Container : constant Entity_Id :=
        Get_Container_In_Iterator_Specification
          (Iterator_Specification
             (Enclosing_Quantified_Expr (Quant_Id)));
      pragma Assert (Present (Container));

      Container_Typ : constant Entity_Id :=
        Retysp (Etype (Container));

   begin
      --  E = A (<value>)

      if Is_Array_Type (Container_Typ) then
         return Source_Name (Container) & " (" & Value  & ")";

      --  E = Element (C, <value>)

      else
         return Refine_Container_Iterator_Value
           (Value, Container_Typ,
            To_Unbounded_String (Source_Name (Container)));
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
     (Cntexmp : Cntexample_File_Maps.Map)
      return Cntexample_File_Maps.Map
   is

      package Supp_Lines is new Ce_Interval_Sets (N => Physical_Line_Number);

      function Get_Interval_Case (N : Node_Id;
                                  B : Boolean)
                                  return Supp_Lines.Interval_Set
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

      function Get_Interval_For_Branch (N : Node_Id)
                                        return Supp_Lines.Interval
        with Pre => Nkind (N) in N_If_Statement | N_Elsif_Part;

      function Get_Interval_For_Branch_Case (N : Node_Id)
                                             return Supp_Lines.Interval
        with Pre => Nkind (N) = N_Case_Statement_Alternative;

      function Get_Interval_If (N : Node_Id;
                                B : Boolean)
                                return Supp_Lines.Interval_Set
        with Pre => Nkind (N) in N_If_Statement | N_Elsif_Part;

      function Get_P (E : Entity_Id) return Physical_Line_Number is
        (Get_Physical_Line_Number (Sloc (E)));
      --  Abbreviation for querying the first line of an entity

      procedure Search_Labels (S : in out Supp_Lines.Interval_Set;
                               L : S_String_List.List;
                               V : Cntexmp_Value_Ptr);
      --  This procedure fills S with new values corresponding to branches that
      --  should not be taken for display of counterexamples.

      -----------------------
      -- Get_Interval_Case --
      -----------------------

      function Get_Interval_Case (N : Node_Id;
                                  B : Boolean)
                                  return Supp_Lines.Interval_Set
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
                 (S, (L_Bound => Get_P (Next (N)),
                      R_Bound =>
                        Get_Physical_Line_Number (
                          End_Location (Enclosing_Statement (N)))));
            end if;

         end if;
         return S;
      end Get_Interval_Case;

      -----------------------------
      -- Get_Interval_For_Branch --
      -----------------------------

      function Get_Interval_For_Branch (N : Node_Id)
                                        return Supp_Lines.Interval
      is
      begin
         if Nkind (N) = N_If_Statement then
            declare
               Lbound : constant Physical_Line_Number :=
                 Get_P (Nlists.First (Then_Statements (N)));
               Rbound : constant Physical_Line_Number :=
                 (if Present (Elsif_Parts (N)) then
                    Get_P (First (Elsif_Parts (N))) - 1

                  elsif Present (Else_Statements (N)) then
                    Get_P (First (Else_Statements (N))) - 1

                  else
                    Get_Physical_Line_Number (End_Location (N)));

            begin
               return (L_Bound => Lbound,
                       R_Bound => Physical_Line_Number'Max (Lbound, Rbound));
            end;

         elsif Nkind (N) = N_Elsif_Part then
            declare
               Lbound : constant Physical_Line_Number :=
                 Get_P (First (Then_Statements (N)));
               Rbound : constant Physical_Line_Number :=
                 (if Present (Next (N)) then
                    Get_P (Next (N)) - 1
                  else
                    (if Present (Else_Statements (Enclosing_Statement (N)))
                     then
                        Get_P (First
                          (Else_Statements (Enclosing_Statement (N))))
                     else
                        Get_Physical_Line_Number
                          (End_Location (Enclosing_Statement (N)))));

            begin
               return (L_Bound => Get_P (First (Then_Statements (N))),
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

      function Get_Interval_For_Branch_Case (N : Node_Id)
                                             return Supp_Lines.Interval
      is
      begin
         if Present (Next (N)) then
            return (L_Bound => Get_P (N),
                    R_Bound =>
                      Physical_Line_Number'Max (1, Get_P (Next (N)) - 1));
         else
            return (L_Bound => Get_P (N),
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

      function Get_Interval_If (N : Node_Id;
                                B : Boolean)
                                return Supp_Lines.Interval_Set
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
                    (S, (L_Bound => Get_P (First (Elsif_Parts (N))),
                         R_Bound =>
                           Get_Physical_Line_Number (End_Location (N))));

               elsif Present (Else_Statements (N)) then
                  Supp_Lines.Insert
                    (S, (L_Bound => Get_P (First (Else_Statements (N))),
                         R_Bound =>
                           Get_Physical_Line_Number (End_Location (N))));
               else

                  --  No elsif or else branch so we don't need to remove
                  --  anything
                  null;
               end if;

            elsif Nkind (N) = N_Elsif_Part then

               if Present (Next (N)) then
                  Supp_Lines.Insert
                    (S, (L_Bound => Get_P (Next (N)),
                         R_Bound =>
                           Get_Physical_Line_Number (
                             End_Location (Enclosing_Statement (N)))));

               else

                  --  If there is no else statements and no following elsif we
                  --  do nothing.

                  if Present (Else_Statements (Enclosing_Statement (N))) then
                     Supp_Lines.Insert
                       (S, (L_Bound =>
                                Get_P (First
                                 (Else_Statements (Enclosing_Statement (N)))),
                            R_Bound =>
                              Get_Physical_Line_Number (
                                End_Location (Enclosing_Statement (N)))));
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

      procedure Search_Labels (S : in out Supp_Lines.Interval_Set;
                               L : S_String_List.List;
                               V : Cntexmp_Value_Ptr)
      is
      begin

         for Elt of L loop
            declare
               Str : constant String := To_String (Elt);
            begin

               if Str'Length > 10 and then
                 Str (Str'First .. Str'First + 9) = "branch_id="
               then

                  declare
                     N : constant Node_Id := Get_Entity_Id
                       (False, Str (Str'First + 10 .. Str'Last));
                  begin
                     if Present (N) and V.T = Cnt_Boolean then

                        if Nkind (N) in N_If_Statement | N_Elsif_Part
                        then
                           Supp_Lines.Insert_Union
                             (S,
                              Get_Interval_If (N, V.Bo));

                        elsif Nkind (N) = N_Case_Statement_Alternative then
                           Supp_Lines.Insert_Union
                             (S,
                              Get_Interval_Case (N, V.Bo));

                        else
                           null;
                        end if;
                     end if;
                  end;
               end if;
            end;
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
                    (Suppressed_Lines,
                     Physical_Line_Number (Line))
                  then
                     Cntexample_Line_Maps.Insert (Cnt_Line_Map, Line,
                                                  Cntexample_Line_Maps.Element
                                                    (Cursor));
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
     (Cntexmp : Cntexample_File_Maps.Map;
      VC_File : String;
      VC_Line : Natural)
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

      --  Insert it at the appropriate location in Remapped_Cntexmp, possibly
      --  deleting other information in the process.

      Remapped_Cntexmp.Insert
        (Key      => VC_File,
         New_Item => (Other_Lines    => Cntexample_Line_Maps.Empty_Map,
                      VC_Line        => Cntexample_Elt_Lists.Empty_List,
                      Previous_Lines => Previous_Line_Maps.Empty_Map),
         Position => C,
         Inserted => Inserted);

      Remapped_Cntexmp (C).Other_Lines.Include (VC_Line, VC);

      return (Remapped_Cntexmp);
   end Remap_VC_Info;

end CE_Display;
