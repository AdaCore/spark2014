with Configuration;
with GNAT.OS_Lib;
with GNATCOLL.VFS; use GNATCOLL.VFS;
with GPR2.Build.Actions.Compile.Ada.Analysis;
with GPR2.Build.Artifacts.Object_File;
with GPR2.Message;
with GPR2.Source_Reference;

package body GPR2.Build.Actions.Compile.Ada.Global_Gen is

   ---------------------
   -- Compute_Command --
   ---------------------

   overriding
   procedure Compute_Command
     (Self           : in out Object;
      Slot           : Positive;
      Cmd_Line       : in out GPR2.Build.Command_Line.Object;
      Signature_Only : Boolean) is
   begin
      GPR2.Build.Actions.Compile.Ada.Object (Self).Compute_Command
        (Slot, Cmd_Line, Signature_Only);
      --  Replace gcc by gnat2why; we need to explicitly remove the previous
      --  command, then add ours.
      Cmd_Line.Remove (0);
      Cmd_Line.Set_Driver ("gnat2why");
      Cmd_Line.Add_Argument ("-gnatc");  --  Do not generate an object file

      --  add special options file
      --  ??? We are not supposed to create temp files if Signature_Only is
      --  false, but we can't know the file name without creating it.
      declare
         Opt_File : constant String :=
           Configuration.Extra_Args_File_For_Unit
             (Self.CU,
              False,
              String (Self.CU.Owning_View.Object_Directory.Value),
              "");
      begin
         Cmd_Line.Add_Argument ("-gnates=" & Opt_File);
      end;
      Cmd_Line.Add_Argument ("-gnatis");  --  Suppress all info messages

      for Arg of Configuration.CL_Switches.Cargs_List loop
         Cmd_Line.Add_Argument (Arg);
      end loop;

   end Compute_Command;

   ------------
   -- Create --
   ------------

   function Create
     (Src : GPR2.Build.Compilation_Unit.Object) return Global_Gen_Id is
   begin
      return
        (GPR2.Build.Actions.Compile.Ada.Ada_Compile_Id'(Ada.Create (Src))
         with null record);
   end Create;

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize
     (Self : in out Object; Unit : GPR2.Build.Compilation_Unit.Object) is
   begin
      GPR2.Build.Actions.Compile.Ada.Object (Self).Initialize (Unit);
      --  The ALI file is the expected output of this action
      Self.Obj_File :=
        GPR2.Build.Artifacts.Object_File.Create (Self.Dep_File.Path);
   end Initialize;

   --------------
   -- Extended --
   --------------

   overriding
   function Extended (Self : Object) return Object is
   begin
      return Self;
   end Extended;

   ------------------
   -- Post_Command --
   ------------------

   overriding
   function Post_Command
     (Self   : in out Object;
      Status : Execution_Status;
      Stdout : Unbounded_String := Null_Unbounded_String;
      Stderr : Unbounded_String := Null_Unbounded_String) return Boolean
   is

      function Add_Global_Gen_Dep (Unit : Name_Type) return Boolean;
      --  Create a global generation action for the given unit and add its ALI
      --  as an input to the analysis actions that depend on the current ALI
      --  file.

      ------------------------
      -- Add_Global_Gen_Dep --
      ------------------------

      function Add_Global_Gen_Dep (Unit : Name_Type) return Boolean is
         CU     : Compilation_Unit.Object;
         GG_Act : GPR2.Build.Actions.Compile.Ada.Global_Gen.Object;

         use type GPR2.Project.View.Object;
      begin
         CU := Self.Ctxt.Namespace_Roots.First_Element.Unit (Unit);

         if not CU.Is_Defined then
            return True;
         end if;

         if Configuration.CL_Switches.No_Subprojects
           and then CU.Owning_View /= Self.CU.Owning_View
         then
            return True;
         end if;

         declare
            GG_Id : constant Global_Gen_Id := Create (CU);
         begin
            if not Self.Tree.Has_Action (GG_Id) then
               GG_Act.Initialize (CU);

               --  Externally built units allow missing ALIs, because they are
               --  optional to analysis actions.
               --  Non-external units must have a valid ALI file.

               if CU.Owning_View.Is_Externally_Built
                 and then not GG_Act.Lib_Ali_File.Path.Exists
               then
                  return True;
               end if;

               if not Self.Tree.Add_Action (GG_Act) then
                  return False;
               end if;
            else
               GG_Act :=
                 GPR2.Build.Actions.Compile.Ada.Global_Gen.Object
                   (Self.Tree.Action (GG_Id));
            end if;
         end;

         --  Make sure that Analysis actions depend on the full closure of
         --  ALIs, which means if GGen A is used by analysis A, and GGen A
         --  depends on GGen B, then Analysis A should also depend on GGen B.

         for Succ of Self.Tree.Successors (Self.Lib_Ali_File) loop
            if Succ in Actions.Compile.Ada.Analysis.Object'Class then
               --  Ensure that GG_Act is always executed before the analysis
               --  action, even if the GG_Act is externally built, as we need
               --  its ALI parsing to be done in the Post_Command.
               Self.Tree.Add_Input (Succ.UID, GG_Act.Lib_Ali_File, True);

               --  Add the ALI file to be used by the analysis action
               Actions.Compile.Ada.Analysis.Object
                 (Self.Tree.Action_Id_To_Reference (Succ.UID).Element.all)
                 .ALI_Files
                 .Include (GG_Act.Lib_Ali_File);
            end if;
         end loop;

         return True;
      end Add_Global_Gen_Dep;

      use GNAT.OS_Lib;
      View : constant Project.View.Object := Self.CU.Owning_View;
   begin
      if Status /= Success then
         return True;
      end if;

      if View.Is_Library and then not View.Is_Externally_Built then
         --  In library projects, copy the generated .ali to the library dir

         declare
            Lib_Dir : Virtual_File renames
              View.Library_Ali_Directory.Virtual_File;
            Success : Boolean;
         begin
            if View.Kind not in With_Object_Dir_Kind
              or else View.Object_Directory.Virtual_File /= Lib_Dir
            then
               Configuration.Create_Dir_And_Parents (Lib_Dir);
               Copy_File
                 (Self.Dep_File.Path.Virtual_File.Display_Full_Name,
                  Lib_Dir.Display_Full_Name,
                  Success,
                  Mode => Overwrite);

               if not Success then
                  Self.Tree.Reporter.Report
                    (GPR2.Message.Create
                       (GPR2.Message.Error,
                        "failed to copy the ALI file to the library directory",
                        GPR2.Source_Reference.Object
                          (GPR2.Source_Reference.Create
                             (Self.Dep_File.Path.Value,
                              Line   => 0,
                              Column => 0))));
                  return False;
               end if;
            end if;
         end;
      end if;

      Self.ALI_Object := GPR2.Build.ALI_Parser.Create (Self.Lib_Ali_File.Path);

      if Self.ALI_Object.Path_Name.Exists then
         Self.ALI_Object.Parse;

         if not Self.ALI_Object.Is_Parsed then
            Self.Tree.Reporter.Report
              (GPR2.Message.Create
                 (GPR2.Message.Error,
                  "failed to analyze the ALI file",
                  GPR2.Source_Reference.Object
                    (GPR2.Source_Reference.Create
                       (Self.ALI_Object.Path_Name.Value,
                        Line   => 0,
                        Column => 0))));
            return False;
         end if;

         for Dep of Self.Withed_Units loop
            if not Add_Global_Gen_Dep (Dep) then
               Self.Tree.Reporter.Report
                 (GPR2.Message.Create
                    (GPR2.Message.Error,
                     "failed to create a Global_Gen action for the dependency"
                     & " unit "
                     & String (Dep)
                     & " obtained after ALI parsing",
                     GPR2.Source_Reference.Object
                       (GPR2.Source_Reference.Create
                          (Self.ALI_Object.Path_Name.Value,
                           Line   => 0,
                           Column => 0))));
               return False;
            end if;
         end loop;
      end if;

      return True;
   end Post_Command;

   ---------
   -- UID --
   ---------

   overriding
   function UID (Self : Object) return Actions.Action_Id'Class is
   begin
      return Global_Gen.Create (Self.CU);
   end UID;

end GPR2.Build.Actions.Compile.Ada.Global_Gen;
