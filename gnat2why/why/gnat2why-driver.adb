------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - D R I V E R                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2016, AdaCore                   --
--                       Copyright (C) 2014-2016, Altran UK Limited         --
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

with Ada.Directories;
with Ada.Strings.Unbounded;    use Ada.Strings.Unbounded;
with Ada.Text_IO;
with AA_Util;                  use AA_Util;
with ALI.Util;                 use ALI.Util;
with ALI;                      use ALI;
with Atree;                    use Atree;
with Binderr;
with Call;
with Common_Containers;        use Common_Containers;
with Debug;                    use Debug;
with Einfo;                    use Einfo;
with Errout;                   use Errout;
with Flow;                     use Flow;
with Flow.Trivia;              use Flow.Trivia;
with Flow_Error_Messages;      use Flow_Error_Messages;
with Flow_Generated_Globals;   use Flow_Generated_Globals;
with Flow_Utility;             use Flow_Utility;
with GNAT.Expect;
with GNAT.Source_Info;
with GNATCOLL.JSON;            use GNATCOLL.JSON;
with Gnat2Why.Annotate;        use Gnat2Why.Annotate;
with Gnat2Why.Assumptions;     use Gnat2Why.Assumptions;
with Gnat2Why.Decls;           use Gnat2Why.Decls;
with Gnat2Why.Error_Messages;  use Gnat2Why.Error_Messages;
with Gnat2Why.External_Axioms; use Gnat2Why.External_Axioms;
with Gnat2Why.Subprograms;     use Gnat2Why.Subprograms;
with Gnat2Why.Types;           use Gnat2Why.Types;
with Gnat2Why.Util;            use Gnat2Why.Util;
with Gnat2Why_Args;
with Lib;                      use Lib;
with Namet;                    use Namet;
with Nlists;                   use Nlists;
with Osint.C;                  use Osint.C;
with Osint;                    use Osint;
with Output;                   use Output;
with Outputs;                  use Outputs;
with Sem;
with Sem_Util;                 use Sem_Util;
with Sinfo;                    use Sinfo;
with Sinput;                   use Sinput;
with SPARK_Definition;         use SPARK_Definition;
with SPARK_Frame_Conditions;   use SPARK_Frame_Conditions;
with SPARK_Rewrite;            use SPARK_Rewrite;
with SPARK_Util;               use SPARK_Util;
with Stand;                    use Stand;
with Switch;                   use Switch;
with Why;                      use Why;
with Why.Atree.Modules;        use Why.Atree.Modules;
with Why.Atree.Sprint;         use Why.Atree.Sprint;
with Why.Atree.Tables;         use Why.Atree.Tables;
with Why.Inter;                use Why.Inter;

pragma Warnings (Off, "unit ""Why.Atree.Treepr"" is not referenced");
with Why.Atree.Treepr;  --  To force the link of debug routines (wpn, wpt)
pragma Warnings (On,  "unit ""Why.Atree.Treepr"" is not referenced");

package body Gnat2Why.Driver is

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Compute_Global_Effects (Current_Unit_Only : Boolean := False);
   --  Make the computed global effects information available for all
   --  subprograms.
   --
   --  If Current_Unit_Only is set then we do not pull in the ALIs of
   --  dependent units.

   procedure Complete_Declaration (E : Entity_Id);
   --  Generate completion for every subprogram or type entity in List_Entities

   function Is_Translated_Subprogram (E : Entity_Id) return Boolean;
   --  @param E Subprogram entity.
   --  @return True iff subprogram E needs to be translated into Why3.

   procedure Translate_CUnit;
   --  Translates the current compilation unit into Why

   procedure Translate_Standard_Package;

   procedure Translate_Entity (E : Entity_Id);
   --  Translates entity E into Why

   procedure Do_Generate_VCs (E : Entity_Id);
   --  Generates VCs for entity E. This is currently a noop for E other than
   --  subprogram, entry, task or package.

   procedure Print_Why_File;
   --  Print the input Why3 file on disk

   procedure Touch_Main_File (Prefix : String);
   --  This procedure is used when there is nothing to do, but it should be
   --  signalled that everything went fine. This is done by creating the main
   --  output file of gnat2why, the main Why file.

   procedure Run_Gnatwhy3;
   --  After generating the Why file, run the proof tool

   procedure Create_JSON_File (Proof_Done : Boolean);
   --  At the very end, write the analysis results to disk

   procedure Generate_Assumptions;
   --  For all calls from a SPARK subprogram to another, register assumptions

   --------------------------
   -- Complete_Declaration --
   --------------------------

   procedure Complete_Declaration (E : Entity_Id) is
   begin
      case Ekind (E) is
         when E_Entry | E_Function | E_Procedure =>
            if Is_Translated_Subprogram (E)

              --  Axioms for a SPARK expression function are issued in the same
              --  module as the function declaration.
              and then (Ekind (E) in Entry_Kind
                        or else not Present (Get_Expression_Function (E))
                        or else not Entity_Body_In_SPARK (E))
            then
               declare
                  Compl_File : constant W_Section_Id :=
                    Dispatch_Entity_Completion (E);
               begin
                  Generate_Subprogram_Completion (Compl_File, E);
               end;
            end if;

            --  An entity E_Subprogram_Body should be present only for
            --  expression functions.
            --  ??? special case of expression functions still necessary ?

         when E_Subprogram_Body =>
            declare
               Decl_E : constant Entity_Id := Unique_Entity (E);
               File   : constant W_Section_Id := Dispatch_Entity (E);
            begin
               pragma Assert (Present (Get_Expression_Function (Decl_E)));

               Translate_Expression_Function_Body (File, Decl_E);
            end;

         when Type_Kind =>
            if Entity_In_SPARK (E)
              and then Retysp (E) = E
              and then not Is_Standard_Boolean_Type (E)
              and then E /= Universal_Fixed
            then
               declare
                  Compl_File : constant W_Section_Id :=
                    Dispatch_Entity_Completion (E);
               begin
                  Generate_Type_Completion (Compl_File, E);
               end;
            end if;

         when E_Package =>
            if Entity_In_Ext_Axioms (E) then
               Complete_External_Entities (E);
            end if;

         when others =>
            null;
      end case;
   end Complete_Declaration;

   ----------------------
   -- Create_JSON_File --
   ----------------------

   procedure Create_JSON_File (Proof_Done : Boolean) is
      FD : Ada.Text_IO.File_Type;
      File_Name : constant String :=
        Ada.Directories.Compose
          (Name      => Unit_Name,
           Extension => "spark");
      Full : constant JSON_Value := Create_Object;
   begin
      Set_Field (Full, "spark", Create (Get_SPARK_JSON));
      Set_Field (Full, "flow", Create (Get_Flow_JSON));
      if Proof_Done then
         Set_Field (Full, "proof", Create (Get_Proof_JSON));
      end if;
      Set_Field (Full, "assumptions", Get_Assume_JSON);

      Ada.Text_IO.Create (FD, Ada.Text_IO.Out_File, File_Name);
      Ada.Text_IO.Put (FD, GNATCOLL.JSON.Write (Full, Compact => False));
      Ada.Text_IO.Close (FD);
   end Create_JSON_File;

   ----------------------------
   -- Compute_Global_Effects --
   ----------------------------

   procedure Compute_Global_Effects (Current_Unit_Only : Boolean := False) is
      Main_Lib_File : File_Name_Type;
      Text          : Text_Buffer_Ptr;
      Main_Lib_Id   : ALI_Id;

   begin

      --  Compute the frame condition. This starts with identifying ALI files
      --  for the current unit and all dependent (with'ed) units. Then SPARK
      --  cross-reference information is loaded from all these files. Finally
      --  the local SPARK cross-reference information is propagated to get
      --  the frame condition. Note that the failure to read an ALI file is
      --  ignored, as it can only correspond to the ALI file of an externally
      --  built unit, for which we use the declared Global contracts.

      Binderr.Initialize_Binderr;
      Initialize_ALI;
      Initialize_ALI_Source;

      --  Fill in table ALIs with all dependent units

      Read_Library_Info (Main_Lib_File, Text);

      if Text = null then
         --  No such ALI file

         Write_Str ("error:" & Get_Name_String (Main_Lib_File) &
                      " does not exist");
         Write_Eol;

         raise Terminate_Program;
      end if;

      Main_Lib_Id := Scan_ALI
        (F                => Main_Lib_File,
         T                => Text,
         Ignore_ED        => False,
         Err              => False,
         Ignore_Errors    => Debug_Flag_I,
         Directly_Scanned => True);
      Free (Text);

      --  If Current_Unit_Only is set then we do NOT load the with'ed
      --  ALI files.
      if Current_Unit_Only then
         declare
            ALI_File_Name : constant File_Name_Type :=
              ALIs.Table (Main_Lib_Id).Afile;
            ALI_File_Name_Str : constant String :=
              Name_String (Name_Id (Full_Lib_File_Name (ALI_File_Name)));
         begin
            Load_SPARK_Xrefs (ALI_File_Name_Str);
         end;
      else
         Read_Withed_ALIs (Main_Lib_Id, Ignore_Errors => True);

         --  Load SPARK cross-reference information from ALIs for all
         --  dependent units.

         for Index in ALIs.First .. ALIs.Last loop
            declare
               ALI_File_Name : constant File_Name_Type :=
                 ALIs.Table (Index).Afile;
               ALI_File_Name_Str : constant String :=
                 Name_String (Name_Id (Full_Lib_File_Name (ALI_File_Name)));
            begin
               Load_SPARK_Xrefs (ALI_File_Name_Str);
            end;
         end loop;
      end if;

      --  Compute the frame condition from raw SPARK cross-reference
      --  information.

      Propagate_Through_Call_Graph (Ignore_Errors     => Current_Unit_Only,
                                    Current_Unit_Only => Current_Unit_Only);
   end Compute_Global_Effects;

   ---------------------
   -- Do_Generate_VCs --
   ---------------------

   procedure Do_Generate_VCs (E : Entity_Id) is
   begin
      --  ??? early return if
      --      Analysis_Requested (E, With_Inlined => False) and then
      --      Entity_Spec_In_SPARK (E)
      case Ekind (E) is
         when Subprogram_Kind | Entry_Kind =>
            if Analysis_Requested (E, With_Inlined => False)
              and then Entity_Spec_In_SPARK (E)

              --  Ignore predicate functions and invariant procedures
              and then not Subprogram_Is_Ignored_For_Proof (E)
            then
               declare
                  LSP_Applies : constant Boolean :=
                    Is_Dispatching_Operation (E) and then
                    not Is_Invisible_Dispatching_Operation (E);
               begin
                  if LSP_Applies then
                     Ada_Ent_To_Why.Push_Scope (Symbol_Table);
                     Update_Symbol_Table_For_Inherited_Contracts (E);
                  end if;

                  --  Generate Why3 code to check absence of run-time errors in
                  --  contracts and body.

                  Generate_VCs_For_Subprogram (WF_Main, E);

                  --  Generate Why3 code to check LSP for primitive of tagged
                  --  types.

                  if LSP_Applies then
                     Generate_VCs_For_LSP (WF_Main, E);
                     Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
                  end if;
               end;
            end if;

         when E_Package =>
            if Entity_Spec_In_SPARK (E) and then
              not Entity_In_Ext_Axioms (E) and then
              Analysis_Requested (E, With_Inlined => False)
            then
               Generate_VCs_For_Package_Elaboration (WF_Main, E);
            end if;

         when E_Task_Type =>
            if Entity_Spec_In_SPARK (E) and then
              Analysis_Requested (E, With_Inlined => False)
            then
               Generate_VCs_For_Task (WF_Main, E);
            end if;

         when others =>
            null;
      end case;
   end Do_Generate_VCs;

   -----------------
   -- GNAT_To_Why --
   -----------------

   procedure GNAT_To_Why (GNAT_Root : Node_Id) is
      N         : constant Node_Id := Unit (GNAT_Root);
      Base_Name : constant String :=
          File_Name_Without_Suffix
            (Get_Name_String (Unit_File_Name (Main_Unit)));

      --  Note that this use of Sem.Walk_Library_Items to see units in an order
      --  which avoids forward references has caused problems in the past with
      --  the combination of generics and inlining, as well as child units
      --  referenced in parent units. To be checked.

      procedure Rewrite_All_Compilation_Units is new Sem.Walk_Library_Items
        (Action => Rewrite_Compilation_Unit);

      procedure Mark_All_Compilation_Units is new Sem.Walk_Library_Items
        (Action => Mark_Compilation_Unit);

      --  this Boolean indicates whether proof have been attempted
      --  anywhere in the unit
      Proof_Done : Boolean := False;

   begin
      if Is_Generic_Unit (Unique_Defining_Entity (N))
        and then Analysis_Requested (Unique_Defining_Entity (N),
                                     With_Inlined => False)
      then

         --  We do nothing for generic units currently. If this get revised
         --  at some point to provide proof of generics, then the special
         --  SPARK expansion in the frontend should be applied to generic
         --  units as well. We still need to create the Why files to
         --  indicate that everything went OK. We also print a warning that
         --  nothing has been done, if the user has specifically requested
         --  analysis of this file.

         if not Gnat2Why_Args.Global_Gen_Mode then
            Touch_Main_File (Base_Name);
         end if;

         return;
      end if;

      Mark_Standard_Package;

      --  Allow the generation of new nodes and lists

      Atree.Unlock;
      Nlists.Unlock;
      Sem.Scope_Stack.Locked := False;
      Lib.Unlock;

      --  Before any analysis takes place, perform some rewritings of the tree
      --  that facilitates analysis.

      Rewrite_All_Compilation_Units;

      --  Mark all compilation units as "in SPARK / not in SPARK", in
      --  the same order that they were processed by the frontend. Bodies
      --  are not included, except for the main unit itself, which always
      --  comes last.

      Mark_All_Compilation_Units;

      --  Set up the flow tree utility package.

      Flow_Utility.Initialize;

      --  Finalize has to be called before we call Compilation_Errors.
      Finalize (Last_Call => False);

      if Compilation_Errors or else Gnat2Why_Args.Check_Mode then
         return;
      end if;

      if Gnat2Why_Args.Global_Gen_Mode then

         --  Compute basic globals. These will be used for subprograms
         --  that are NOT in SPARK.
         Compute_Global_Effects (Current_Unit_Only => True);

         if not Gnat2Why_Args.Debug_Proof_Only then
            Generate_Flow_Globals (GNAT_Root);
         end if;

      else

         --  Compute basic globals
         Compute_Global_Effects;

         --  Read the generated globals from the ALI files
         GG_Read (GNAT_Root);

         --  Do some flow analysis

         if not Gnat2Why_Args.Debug_Proof_Only then
            Flow_Analyse_CUnit (GNAT_Root);
            Generate_Assumptions;
         end if;

         --  Start the translation to Why

         if not Gnat2Why_Args.Flow_Analysis_Mode
           and then Is_In_Analyzed_Files (N)
         then
            Proof_Done := True;
            Why.Atree.Modules.Initialize;
            Init_Why_Sections;
            Translate_Standard_Package;
            Translate_CUnit;
            Run_Gnatwhy3;
            if Gnat2Why_Args.Limit_Line = Null_Unbounded_String then
               Generate_Useless_Pragma_Annotate_Warnings;
            end if;
         end if;
         Create_JSON_File (Proof_Done);
      end if;

   end GNAT_To_Why;

   --------------------------
   -- Generate_Assumptions --
   --------------------------

   procedure Generate_Assumptions is
   begin
      for E of Marked_Entities loop
         case Ekind (E) is
            when Subprogram_Kind =>
               if SPARK_Util.Analysis_Requested (E, With_Inlined => True)
                 and then Entity_Body_In_SPARK (E)
               then
                  for C of Direct_Calls (E) loop
                     Register_Assumptions_For_Call (E, C);
                  end loop;
               end if;

            when E_Package =>

               --  ??? we need to do the same for packages, we would have to
               --  take into account calls during elaboration, and elaboration
               --  of the with'ed packages

               null;

            when others =>
               null;
         end case;
      end loop;
   end Generate_Assumptions;

   ------------------------
   -- Is_Back_End_Switch --
   ------------------------

   function Is_Back_End_Switch (Switch : String) return Boolean is
      First : constant Positive := Switch'First + 1;

   begin
      --  For now we allow the -g/-O/-f/-m/-W/-w switches, even though they
      --  will have no effect.
      --  This permits compatibility with existing scripts.

      return
        Is_Switch (Switch) and then
        Switch (First) in 'f' | 'g' | 'm' | 'O' | 'W' | 'w';
   end Is_Back_End_Switch;

   ------------------------------
   -- Is_Translated_Subprogram --
   ------------------------------

   function Is_Translated_Subprogram (E : Entity_Id) return Boolean is
     (Entity_In_SPARK (E)

       --  Ignore inlined subprograms. Either these are not analyzed
       --  (when referenced and analysis was not specifically requested
       --  for them), in which case it's safer to skip a declaration
       --  which could be called. Or they are analyzed, but there is
       --  no call to them anyway, so skipping the declaration is safe.

       and then not Is_Local_Subprogram_Always_Inlined (E)

       --  Ignore predicate functions and invariant procedures

       and then not Subprogram_Is_Ignored_For_Proof (E)

       --  Subprograms entities of actual parameter of generic packages with
       --  external axioms are only needed for check of runtime errors.

       and then not (Ekind (E) /= E_Entry
                     and then Is_Generic_Actual_Subprogram (E)
                     and then Entity_In_Ext_Axioms (E))

       --  Ignore simple shifts and rotates

       and then not Is_Simple_Shift_Or_Rotate (E));

   --------------------
   -- Print_Why_File --
   --------------------

   procedure Print_Why_File is
   begin
      Open_Current_File (Why_File_Name.all);
      for WF in W_Section_Id loop
         Print_Section (Why_Sections (WF), Current_File);
      end loop;
      Close_Current_File;
   end Print_Why_File;

   ------------------
   -- Run_Gnatwhy3 --
   ------------------

   procedure Run_Gnatwhy3 is
      use Ada.Directories;
      Status  : aliased Integer;
      Fn      : constant String :=
        Compose (Current_Directory, Why_File_Name.all);
      Old_Dir : constant String := Current_Directory;

   begin
      if Has_Registered_VCs then
         Set_Directory (To_String (Gnat2Why_Args.Why3_Dir));
         Gnat2Why_Args.Why3_Args.Append (Fn);

         if Gnat2Why_Args.Debug_Mode then
            Ada.Text_IO.Put ("gnatwhy3 ");
            for Elt of Gnat2Why_Args.Why3_Args loop
               Ada.Text_IO.Put (Elt);
               Ada.Text_IO.Put (" ");
            end loop;
            Ada.Text_IO.New_Line;
         end if;

         Parse_Why3_Results
           (GNAT.Expect.Get_Command_Output
              ("gnatwhy3",
               Call.Argument_List_Of_String_List (Gnat2Why_Args.Why3_Args),
               Err_To_Out => False,
               Input      => "",
               Status     => Status'Access));
         Set_Directory (Old_Dir);
      end if;
   end Run_Gnatwhy3;

   ---------------------
   -- Touch_Main_File --
   ---------------------

   procedure Touch_Main_File (Prefix : String) is
      Filename : constant String := Prefix & Why_File_Suffix;
   begin
      Open_Current_File (Filename);
      Close_Current_File;
   end Touch_Main_File;

   ---------------------
   -- Translate_CUnit --
   ---------------------

   procedure Translate_CUnit is

      procedure For_All_Entities
        (Process : not null access procedure (E : Entity_Id));
      --  Traversal procedure to process entities which need translation

      procedure Generate_VCs (E : Entity_Id);
      --  Check if E is in main unit and then generate VCs

      ----------------------
      -- For_All_Entities --
      ----------------------

      procedure For_All_Entities
        (Process : not null access procedure (E : Entity_Id))
      is
      begin
         for E of Entities_To_Translate loop
            Process (E);
         end loop;
      end For_All_Entities;

      ------------------
      -- Generate_VCs --
      ------------------

      procedure Generate_VCs (E : Entity_Id) is
      begin
         if In_Main_Unit (E) then
            Do_Generate_VCs (E);
         end if;
      end Generate_VCs;

   --  Start of processing for Translate_CUnit

   begin
      --  Translate Ada entities into Why3

      For_All_Entities (Translate_Entity'Access);

      --  For all objects whose declaration is not visible (has not been
      --  translated to Why), we generate a dummy declaration. This must
      --  be done after translating above entities.

      For_All_External_Objects (Translate_External_Object'Access);

      --  For all state abstractions whose declaration is not visible (has not
      --  been translated to Why), we generate a dummy declaration.

      For_All_External_States (Translate_External_Object'Access);

      For_All_Entities (Complete_Declaration'Access);

      --  Generate VCs for entities of unit. This must follow the generation of
      --  modules for entities, so that all completions for deferred constants
      --  and expression functions are defined.

      For_All_Entities (Generate_VCs'Access);

      Print_Why_File;
   end Translate_CUnit;

   ----------------------
   -- Translate_Entity --
   ----------------------

   procedure Translate_Entity (E : Entity_Id) is

      procedure Generate_Empty_Axiom_Theory
        (File : W_Section_Id;
         E    : Entity_Id);
      --  Generates an empty theory for the axiom related to E. This is done
      --  for every entity for which there is no axiom theory generated, so
      --  that modules for VC generation can consistently include the axiom
      --  theory of all they entities they use.

      ---------------------------------
      -- Generate_Empty_Axiom_Theory --
      ---------------------------------

      procedure Generate_Empty_Axiom_Theory
        (File : W_Section_Id;
         E    : Entity_Id) is
      begin
         Open_Theory
           (File, E_Axiom_Module (E),
            Comment =>
              "Module giving an empty axiom for the entity "
                & """" & Get_Name_String (Chars (E)) & """"
                & (if Sloc (E) > 0 then
                    " defined at " & Build_Location_String (Sloc (E))
                   else "")
                & ", created in " & GNAT.Source_Info.Enclosing_Entity);
         Close_Theory (File,
                       Kind => Standalone_Theory);
      end Generate_Empty_Axiom_Theory;

      File       : constant W_Section_Id := Dispatch_Entity (E);
      Compl_File : constant W_Section_Id := Dispatch_Entity_Completion (E);
      New_Theory : Boolean;

   --  Start of processing for Translate_Entity

   begin
      case Ekind (E) is

         when Type_Kind =>

            --  For a type with partial and full view, both entities will be
            --  encountered here, but only one should be translated. We pick
            --  the one with the most information that's still in SPARK.

            if Entity_In_SPARK (E)
              and then Retysp (E) = E
            then
               --  Partial views of private types should not be
               --  translated if the underlying type is not in SPARK,
               --  otherwise we end up with two definitions for the same
               --  private type.

               Translate_Type (File, E, New_Theory);
            end if;

         when Named_Kind =>
            if Entity_In_SPARK (E) then
               Translate_Constant (File, E);
               Translate_Constant_Value (Compl_File, E);
            end if;

         when Object_Kind =>

            --  we can ignore discriminals, these are objects used for
            --  analysis, that can occur for discriminants of protected
            --  types and task types

            if Ekind (E) in Formal_Kind
              and then Present (Discriminal_Link (E))
                and then Ekind (Scope (E)) in Protected_Kind | Task_Kind
            then
               return;
            end if;

            --  Fill the set of translated object entities and do not generate
            --  a dummy declaration for those.

            Translated_Object_Entities.Include (To_Entity_Name (E));

            --  Constants and variables are translated differently

            if not Is_Mutable_In_Why (E) then
               if Entity_In_SPARK (E) then
                  if Ekind (E) = E_Constant then
                     if Is_Partial_View (E) then
                        Translate_Constant (File, E);
                        if not Entity_In_SPARK (Full_View (E)) then
                           Generate_Empty_Axiom_Theory (File, E);
                        end if;
                     elsif Is_Full_View (E) then
                        Translate_Constant_Value (Compl_File, E);
                     else
                        Translate_Constant (File, E);
                        Translate_Constant_Value (Compl_File, E);
                     end if;
                  else
                     Translate_Constant (File, E);
                     Generate_Empty_Axiom_Theory (File, E);
                  end if;
               end if;

            --  variables that are part of a protected object are not
            --  translated separately

            elsif Is_Part_Of_Protected_Object (E) then
               null;
            else
               Translate_Variable (File, E);
               Generate_Empty_Axiom_Theory (File, E);
            end if;

         when E_Abstract_State =>
            Translate_Abstract_State (File, E);
            Generate_Empty_Axiom_Theory (File, E);

         --  Generate a logic function for Ada functions

         when Subprogram_Kind | Entry_Kind =>
            if Is_Translated_Subprogram (E) then
               Translate_Subprogram_Spec (File, E);
            end if;

         when E_Subprogram_Body =>
            null;

         --  Given to the handler for packages with an associated theory

         when E_Package =>
            if Entity_In_Ext_Axioms (E) then
               Translate_Package_With_External_Axioms (E);
            else

               --  ??? We should deal with elaboration at this point
               --  See M618-009

               null;
            end if;

         when E_Loop =>
            Translate_Loop_Entity (File, E);
            Generate_Empty_Axiom_Theory (File, E);

         when others =>
            raise Program_Error;
      end case;
   end Translate_Entity;

   --------------------------------
   -- Translate_Standard_Package --
   --------------------------------

   procedure Translate_Standard_Package is

      procedure Translate (E : Entity_Id);
      --  Translate and complete declaration of entity E

      ---------------
      -- Translate --
      ---------------

      procedure Translate (E : Entity_Id) is
      begin
         Translate_Entity (E);
         Complete_Declaration (E);
      end Translate;

      Decl : Node_Id :=
        First (Visible_Declarations (Specification (Standard_Package_Node)));

   --  Start of processing for Translate_Standard_Package

   begin
      while Present (Decl) loop
         case Nkind (Decl) is
            when N_Full_Type_Declaration |
                 N_Subtype_Declaration   |
                 N_Object_Declaration    =>
               Translate (Defining_Entity (Decl));
            when others =>
               null;
         end case;

         Next (Decl);
      end loop;

      --  The following types are not in the tree of the standard package, but
      --  still are referenced elsewhere.

      Translate (Standard_Integer_8);
      Translate (Standard_Integer_16);
      Translate (Standard_Integer_32);
      Translate (Standard_Integer_64);
      Translate (Universal_Integer);
      Translate (Universal_Real);

   end Translate_Standard_Package;

end Gnat2Why.Driver;
