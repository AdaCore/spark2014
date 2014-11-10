------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - D R I V E R                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2014, AdaCore                   --
--                       Copyright (C) 2014, Altran UK Limited              --
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

with GNAT.Source_Info;
with GNAT.Expect;

with Ada.Directories;
with Ada.Strings.Unbounded;    use Ada.Strings.Unbounded;
with AA_Util;                  use AA_Util;
with ALI.Util;                 use ALI.Util;
with ALI;                      use ALI;
with Atree;                    use Atree;
with Binderr;
with Call;
with Debug;                    use Debug;
with Einfo;                    use Einfo;
with Errout;                   use Errout;
with Flow;                     use Flow;
with Flow.Trivia;              use Flow.Trivia;
with Flow_Error_Messages;      use Flow_Error_Messages;
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
with Stand;                    use Stand;
with Switch;                   use Switch;

with SPARK_Definition;         use SPARK_Definition;
with SPARK_Rewrite;            use SPARK_Rewrite;
with SPARK_Frame_Conditions;   use SPARK_Frame_Conditions;
with SPARK_Util;               use SPARK_Util;

with Why;                      use Why;
with Why.Atree.Modules;        use Why.Atree.Modules;
with Why.Atree.Sprint;         use Why.Atree.Sprint;
with Why.Gen.Names;            use Why.Gen.Names;
with Why.Inter;                use Why.Inter;
with Why.Types;                use Why.Types;

with Common_Containers;        use Common_Containers;
with GNATCOLL.JSON;            use GNATCOLL.JSON;
with Gnat2Why.Decls;           use Gnat2Why.Decls;
with Gnat2Why.Error_Messages;  use Gnat2Why.Error_Messages;
with Gnat2Why.External_Axioms; use Gnat2Why.External_Axioms;
with Gnat2Why.Nodes;           use Gnat2Why.Nodes;
with Gnat2Why_Args;
with Gnat2Why.Assumptions;     use Gnat2Why.Assumptions;
with Gnat2Why.Subprograms;     use Gnat2Why.Subprograms;
with Gnat2Why.Types;           use Gnat2Why.Types;
with Gnat2Why.Util;            use Gnat2Why.Util;

with Flow_Computed_Globals;    use Flow_Computed_Globals;

pragma Warnings (Off, "unit ""Why.Atree.Treepr"" is not referenced");
with Why.Atree.Treepr;  --  To force the link of debug routines (wpn, wpt)
pragma Warnings (On,  "unit ""Why.Atree.Treepr"" is not referenced");
with Ada.Text_IO;

package body Gnat2Why.Driver is

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Compute_Global_Effects;
   --  Make the computed global effects information available for all
   --  subprograms

   procedure Translate_CUnit;
   --  Translates the current compilation unit into Why

   procedure Translate_Standard_Package;

   procedure Translate_Entity (E : Entity_Id);
   --  Translates entity E into Why

   procedure Do_Generate_VCs (E : Entity_Id);
   --  Generates VCs for entity E. This is currently a noop if E is not a
   --  subprogram or a package.

   procedure Print_Why_File;
   --  Print the input Why3 file on disk

   procedure Touch_Main_File (Prefix : String);
   --  This procedure is used when there is nothing to do, but it should be
   --  signalled that everything went fine. This is done by creating the main
   --  output file of gnat2why, the main Why file.

   procedure Run_Gnatwhy3;
   --  After generating the Why file, run the proof tool

   procedure Create_JSON_File (Proof_Done : Boolean);
   --  at the very end, write the analysis results to disk

   procedure Generate_Assumptions;
   --  for all calls from a SPARK subprogram to another, register assumptions

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

   procedure Compute_Global_Effects is
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
      Read_Withed_ALIs (Main_Lib_Id, Ignore_Errors => True);

      --  Load SPARK cross-reference information from ALIs for all dependent
      --  units.

      for Index in ALIs.First .. ALIs.Last loop
         declare
            ALI_File_Name : constant File_Name_Type :=
              ALIs.Table (Index).Afile;
            ALI_File_Name_Str : constant String :=
              Name_String (Name_Id (Full_Lib_File_Name (ALI_File_Name)));
            Has_SPARK_Xrefs : Boolean;
         begin
            Load_SPARK_Xrefs (ALI_File_Name_Str, Has_SPARK_Xrefs);

            if Has_SPARK_Xrefs then
               Loaded_ALI_Files.Include (ALI_File_Name);
            end if;
         end;
      end loop;

      --  Compute the frame condition from raw SPARK cross-reference
      --  information.

      Propagate_Through_Call_Graph (Ignore_Errors => False);
   end Compute_Global_Effects;

   ---------------------
   -- Do_Generate_VCs --
   ---------------------

   procedure Do_Generate_VCs (E : Entity_Id) is
   begin
      if Ekind (E) in Subprogram_Kind
        and then Analysis_Requested (E)
        and then Entity_Spec_In_SPARK (E)

        --  Ignore predicate functions and invariant procedures

        and then not Subprogram_Is_Ignored_For_Proof (E)
      then
         if Is_Dispatching_Operation (E) then
            Ada_Ent_To_Why.Push_Scope (Symbol_Table);
            Update_Symbol_Table_For_Inherited_Contracts (E);
         end if;

         --  Generate Why3 code to check absence of run-time errors in
         --  contracts and body.

         Generate_VCs_For_Subprogram (Why_Sections (WF_Main), E);

         --  Generate Why3 code to check LSP for primitive of tagged types

         if Is_Dispatching_Operation (E) then
            Generate_VCs_For_LSP (Why_Sections (WF_Main), E);
            Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
         end if;

      elsif Ekind (E) = E_Package
              and then
            (if Present (Get_Package_Body (E)) then
               Entity_Body_In_SPARK (E)
             else
               Entity_Spec_In_SPARK (E))
      then
         Generate_VCs_For_Package_Elaboration (Why_Sections (WF_Main), E);
      end if;
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

      --  these booleans indicate whether flow/proof have been attempted
      --  anywhere in the unit

      Proof_Done : Boolean := False;

   begin

      if Is_Generic_Unit (Unique_Defining_Entity (N))
        and then Analysis_Requested (Unique_Defining_Entity (N))
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
            if Gnat2Why_Args.Single_File then
               Error_Msg_N (N   => GNAT_Root,
                            Msg => "!Generic unit is not analyzed");
            end if;
         end if;
         return;

      end if;

      --  All temporaries created for this unit should be different from
      --  temporaries created for other units. To that end, use the unit name
      --  as a suffix for creating temporary names.

      New_Temp_Identifier_Suffix :=
        To_Unbounded_String (Full_Name (Defining_Entity (N)));

      Mark_Standard_Package;

      --  Allow the generation of new nodes and lists

      Atree.Unlock;
      Nlists.Unlock;

      --  Before any analysis takes place, perform some rewritings of the tree
      --  that facilitates analysis.

      Rewrite_All_Compilation_Units;

      --  Mark all compilation units with "in SPARK / not in SPARK" marks, in
      --  the same order that they were processed by the frontend. Bodies
      --  are not included, except for the main unit itself, which always
      --  comes last.

      Mark_All_Compilation_Units;

      if Gnat2Why_Args.Global_Gen_Mode then

         Generate_Flow_Globals (GNAT_Root);

      else

         --  Finalize has to be called before we call Compilation_Errors.
         Finalize (Last_Call => False);

         if Compilation_Errors or else Gnat2Why_Args.Check_Mode then
            return;
         end if;

         --  Compute basic globals
         Compute_Global_Effects;

         --  Add computation of flow globals here
         GG_Read (GNAT_Root);

         --  Do some flow analysis

         if not Gnat2Why_Args.Debug_Proof_Only then
            Flow_Analyse_CUnit;
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
         end if;

      end if;

      Create_JSON_File (Proof_Done);
   end GNAT_To_Why;

   --------------------------
   -- Generate_Assumptions --
   --------------------------

   procedure Generate_Assumptions is
   begin
      for E of Entity_Set loop
         case Ekind (E) is
            when Subprogram_Kind =>
               if SPARK_Util.Analysis_Requested (E)
                 and then Entity_Body_In_SPARK (E)
                 and then Entity_Body_Valid_SPARK (E)
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
      Last  : Natural           := Switch'Last;
   begin
      if Last >= First
        and then Switch (Last) = ASCII.NUL
      then
         Last := Last - 1;
      end if;

      if not Is_Switch (Switch) then
         return False;
      end if;

      --  For now we allow the -g/-O/-f/-m/-W/-w switches, even though they
      --  will have no effect.
      --  This permits compatibility with existing scripts.

      case Switch (First) is
         when 'f' | 'g' | 'm' | 'O' | 'W' | 'w' =>
            return True;

         when others =>
            return False;
      end case;
   end Is_Back_End_Switch;

   --------------------
   -- Print_Why_File --
   --------------------

   procedure Print_Why_File is
   begin
      Open_Current_File (Why_File_Name.all);
      for WF in Why_Section_Enum loop
         Sprint_Why_Node (Why_Node_Id (Why_Sections (WF).File), Current_File);
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

      procedure Complete_Subprograms (List_Entities : Node_Lists.List);
      --  Generate completion for every subprogram entity in List_Entities

      procedure Translate_List_Entities (List_Entities : Node_Lists.List);
      --  Translate the list of entities from the spec or body, in batches, in
      --  order to ensure proper definition before use in Why files.

      --------------------------
      -- Complete_Subprograms --
      --------------------------

      procedure Complete_Subprograms (List_Entities : Node_Lists.List) is
      begin
         for E of List_Entities loop
            if Ekind (E) in Subprogram_Kind
              and then Entity_In_SPARK (E)
              and then not Is_Local_Subprogram_Always_Inlined (E)
              and then not Subprogram_Is_Ignored_For_Proof (E)
              and then (not (Present (Get_Expression_Function (E)))
                        or else not Entity_Body_In_SPARK (E))
            then
               declare
                  Compl_File : Why_Section :=
                    Why_Sections (Dispatch_Entity_Completion (E));
               begin
                  Generate_Subprogram_Completion (Compl_File, E);
               end;

               --  An entity E_Subprogram_Body should be present only for
               --  expression functions.
               --  ??? special case of expression functions still necessary ?

            elsif Ekind (E) = E_Subprogram_Body then
               declare
                  Decl_E : constant Entity_Id := Unique_Entity (E);
                  File   : Why_Section :=
                    Why_Sections (Dispatch_Entity (E));
               begin
                  pragma Assert (Present (Get_Expression_Function (Decl_E)));

                  Translate_Expression_Function_Body (File, Decl_E);
               end;
            end if;
         end loop;
      end Complete_Subprograms;

      -----------------------------
      -- Translate_List_Entities --
      -----------------------------

      procedure Translate_List_Entities (List_Entities : Node_Lists.List) is
      begin
         for E of List_Entities loop
            Translate_Entity (E);
         end loop;
      end Translate_List_Entities;

   --  Start of Translate_CUnit

   begin
      --  Translate Ada entities into Why3

      Translate_List_Entities (Entity_List);

      Complete_Subprograms (Entity_List);

      --  For all objects whose declaration is not visible (has not been
      --  translated to Why), we generate a dummy declaration. This must
      --  be done after translating above entities.

      For_All_External_Objects (Translate_External_Object'Access);

      --  Generate VCs for entities of unit. This must follow the generation of
      --  modules for entities, so that all completions for deferred constants
      --  and expression functions are defined.

      for E of Entity_List loop
         if Is_In_Current_Unit (E) then
            Do_Generate_VCs (E);
         end if;
      end loop;

      Print_Why_File;
   end Translate_CUnit;

   ----------------------
   -- Translate_Entity --
   ----------------------

   procedure Translate_Entity (E : Entity_Id) is

      procedure Generate_Empty_Axiom_Theory
        (File : in out Why_Section;
         E    : Entity_Id);
      --  Generates an empty theory for the axiom related to E. This is done
      --  for every entity for which there is no axiom theory generated, so
      --  that modules for VC generation can consistently include the axiom
      --  theory of all they entities they use.

      ---------------------------------
      -- Generate_Empty_Axiom_Theory --
      ---------------------------------

      procedure Generate_Empty_Axiom_Theory
        (File : in out Why_Section;
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

      File       : Why_Section := Why_Sections (Dispatch_Entity (E));
      Compl_File : Why_Section :=
        Why_Sections (Dispatch_Entity_Completion (E));
      New_Theory : Boolean;

   --  Start of Translate_Entity

   begin
      case Ekind (E) is
         when Type_Kind =>

            --  For a type with partial and full view, both entities will be
            --  encountered here, but only one should be translated. We pick
            --  the one with the most information that's still in SPARK.

            if Entity_In_SPARK (E)
              and then (Is_Full_View (E)
                        or else No (Full_View (E))
                        or else Fullview_Not_In_SPARK (E))
            then
               Translate_Type (File, E, New_Theory);
               if New_Theory then
                  Generate_Type_Completion (Compl_File, E);
               end if;
            end if;

         when Named_Kind =>
            if Entity_In_SPARK (E) then
               Translate_Constant (File, E);
               Translate_Constant_Value (Compl_File, E);
            end if;

         when Object_Kind =>

            --  We need to fill the set of translated object entities, so that
            --  we do not generate a dummy declaration for those

            declare
               Ent_Name : constant Entity_Name := new String'(Unique_Name (E));
            begin
               Translated_Object_Entities.Include (Ent_Name);
            end;

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

            else
               Translate_Variable (File, E);
               Generate_Empty_Axiom_Theory (File, E);
            end if;

         when E_Abstract_State =>
            Translate_Abstract_State (File, E);
            Generate_Empty_Axiom_Theory (File, E);

         when Subprogram_Kind =>
            if Entity_In_SPARK (E)

              --  Ignore inlined subprograms. Either these are not analyzed
              --  (when referenced and analysis was not specifically requested
              --  for them), in which case it's safer to skip a declaration
              --  which could be called. Or they are analyzed, but there is
              --  no call to them anyway, so skipping the declaration is safe.

              and then not Is_Local_Subprogram_Always_Inlined (E)

              --  Ignore predicate functions and invariant procedures

              and then not Subprogram_Is_Ignored_For_Proof (E)

              --  Subprograms entities of actual parameter of generic packages
              --  with external axioms are only needed for check of runtime
              --  errors.

              and then not (Is_Generic_Actual_Subprogram (E) and then
                            Entity_In_External_Axioms (E))
            then

               --  Generate a logic function for Ada functions

               Translate_Subprogram_Spec (File, E);
            end if;

         when E_Subprogram_Body =>
            null;

         --  Given to the handler for packages with an associated theory

         when E_Package =>
            if Entity_In_External_Axioms (E) then
               Translate_Package_With_External_Axioms (E);
            else

               --  ??? We should deal with elaboration at this point
               --  See M618-019

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
      Decl : Node_Id :=
        First (Visible_Declarations (Specification (Standard_Package_Node)));
   begin
      while Present (Decl) loop
         case Nkind (Decl) is
            when N_Full_Type_Declaration |
                 N_Subtype_Declaration   |
                 N_Object_Declaration    =>
               Translate_Entity (Defining_Entity (Decl));
            when others =>
               null;
         end case;

         Next (Decl);
      end loop;

      --  The following types are not in the tree of the standard package, but
      --  still are referenced elsewhere

      Translate_Entity (Standard_Integer_8);
      Translate_Entity (Standard_Integer_16);
      Translate_Entity (Standard_Integer_32);
      Translate_Entity (Standard_Integer_64);
      Translate_Entity (Universal_Integer);
      Translate_Entity (Universal_Real);

   end Translate_Standard_Package;

end Gnat2Why.Driver;
