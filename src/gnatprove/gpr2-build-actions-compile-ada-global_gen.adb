with Configuration;
with GNAT.OS_Lib;
with GNATCOLL.VFS; use GNATCOLL.VFS;
with GPR2.Build.Artifacts.Object_File;

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
      --  replace gcc by gnat2why
      Cmd_Line.Set_Driver ("gnat2why");
      Cmd_Line.Remove (1);
      Cmd_Line.Add_Argument ("-gnatc");  --  Do not generate an object file

      --  add special options file
      Cmd_Line.Add_Argument ("-gnates=" & To_String (Self.Opt_File));
      Cmd_Line.Add_Argument ("-gnatis");  --  Suppress all info messages

      for Arg of Configuration.CL_Switches.Cargs_List loop
         Cmd_Line.Add_Argument (Arg);
      end loop;

   end Compute_Command;

   function Create
     (Src : GPR2.Build.Compilation_Unit.Object) return Global_Gen_Id is
   begin
      return
        (GPR2.Build.Actions.Compile.Ada.Ada_Compile_Id'(Ada.Create (Src))
         with null record);
   end Create;

   procedure Initialize
     (Self     : in out Object;
      Unit     : GPR2.Build.Compilation_Unit.Object;
      Opt_File : String) is
   begin
      GPR2.Build.Actions.Compile.Ada.Object (Self).Initialize (Unit);
      Self.Opt_File := To_Unbounded_String (Opt_File);
      --  The ALI file is the expected output of this action
      Self.Obj_File :=
        GPR2.Build.Artifacts.Object_File.Create (Self.Dep_File.Path);
   end Initialize;

   overriding
   function Extended (Self : Object) return Object is
   begin
      return Result : Object := Self do
         Result.Opt_File := Null_Unbounded_String;
      end return;
   end Extended;

   overriding
   function Post_Command
     (Self   : in out Object;
      Status : Execution_Status;
      Stdout : Unbounded_String := Null_Unbounded_String;
      Stderr : Unbounded_String := Null_Unbounded_String) return Boolean
   is
      use GNAT.OS_Lib;
      Success : Boolean := True;
      View    : constant Project.View.Object := Self.CU.Owning_View;
   begin
      --  ??? Do we need to call the parent Post_Command?

      --  In library projects, copy the generated .ali to the library dir
      if View.Is_Library then
         declare
            Lib_Dir : Virtual_File renames
              View.Library_Ali_Directory.Virtual_File;
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
            end if;
         end;
      end if;
      pragma Assert (Success, "Failed to copy .ali file to library directory");
      return Success;
   end Post_Command;

   overriding
   function UID (Self : Object) return Actions.Action_Id'Class is
   begin
      return Global_Gen.Create (Self.CU);
   end UID;

end GPR2.Build.Actions.Compile.Ada.Global_Gen;
