with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Ada.Text_IO;
with Configuration;
with GNAT.Strings;          use GNAT.Strings;
with GPR2.Build.Artifacts.Files;
with GPR2.Build.Artifacts.Source_Files;
with VC_Kinds;              use VC_Kinds;

package body GPR2.Build.Actions.Compile.Ada.Data_Rep is

   ----------------
   -- Applicable --
   ----------------

   function Applicable (CU : GPR2.Build.Compilation_Unit.Object) return Boolean
   is
   begin
      --  ??? We skip multi unit sources for now. Note that this never worked.
      return
        Configuration.Mode not in GPM_Check | GPM_Check_All | GPM_Flow
        and then CU.Main_Part.Index = No_Index
        and then not Configuration.Has_gnateT_Switch (CU.Owning_View)
        and then
          (Configuration.GnateT_Switch = null
           or else Configuration.GnateT_Switch.all = "");
   end Applicable;

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

      --  Prepend the wrapper; the original compiler becomes its first
      --  argument so it can delegate the actual compilation.
      Cmd_Line.Set_Driver ("spark_data_rep_wrapper");

      if Configuration.Verbose then
         Cmd_Line.Add_Argument ("--verbose");
      elsif Configuration.Quiet then
         Cmd_Line.Add_Argument ("--quiet");
      end if;

      --  Generate data-representation JSON
      Cmd_Line.Add_Argument ("-gnatR2js");
      Cmd_Line.Add_Argument ("-gnatws");   --  Suppress warnings
      Cmd_Line.Add_Argument ("-gnatx");    --  Suppress cross-reference info
      Cmd_Line.Add_Argument ("-gnatis");   --  Suppress info messages
      Cmd_Line.Add_Argument ("-gnatd_A");  --  Suppress ALI file generation

      --  ??? -S disables the generation of object files, but instead generates
      --  an assembly file, which is cheaper. Ideally we would like none of
      --  those.
      Cmd_Line.Add_Argument ("-S");

      if Configuration.GnateT_Switch /= null
        and then Configuration.GnateT_Switch.all /= ""
      then
         Cmd_Line.Add_Argument (Configuration.GnateT_Switch.all);
      end if;

      for Arg of Configuration.CL_Switches.Cargs_List loop
         Cmd_Line.Add_Argument (Arg);
      end loop;
   end Compute_Command;

   ------------
   -- Create --
   ------------

   function Create
     (Src : GPR2.Build.Compilation_Unit.Object) return Data_Rep_Id is
   begin
      return
        (GPR2.Build.Actions.Compile.Ada.Ada_Compile_Id'(Ada.Create (Src))
         with null record);
   end Create;

   --------------
   -- Extended --
   --------------

   overriding
   function Extended (Self : Object) return Object is
   begin
      return Self;
   end Extended;

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize
     (Self : in out Object; Unit : GPR2.Build.Compilation_Unit.Object) is
   begin
      GPR2.Build.Actions.Compile.Ada.Object (Self).Initialize (Unit);
   end Initialize;

   ---------------------------
   -- Data_Rep_File_For_Unit --
   ---------------------------

   function Data_Rep_File_For_Unit
     (CU : GPR2.Build.Compilation_Unit.Object)
      return GPR2.Build.Artifacts.Files.Object is
   begin
      return
        GPR2.Build.Artifacts.Files.Create
          (CU.Owning_View.Object_Directory.Compose
             (Filename_Type
                (String (CU.Main_Part.Source.Simple_Name) & ".json")));
   end Data_Rep_File_For_Unit;

   -----------------
   -- JSON_Output --
   -----------------

   function JSON_Output
     (Self : Object) return GPR2.Build.Artifacts.Files.Object is
   begin
      return Data_Rep_File_For_Unit (Self.CU);
   end JSON_Output;

   -----------------------
   -- On_Tree_Insertion --
   -----------------------

   overriding
   function On_Tree_Insertion
     (Self : Object; Db : in out GPR2.Build.Tree_Db.Object) return Boolean
   is
      UID      : constant Actions.Action_Id'Class := Object'Class (Self).UID;
      JSON_Out : constant GPR2.Build.Artifacts.Files.Object :=
        Self.JSON_Output;
   begin
      Db.Add_Input
        (UID,
         GPR2.Build.Artifacts.Source_Files.Create (Self.Src.Path_Name),
         True);

      --  Depend on the ALI file produced by the global-generation phase for
      --  this unit, so that data-representation generation is only executed
      --  when that phase succeeded.  A compilation error causes that phase to
      --  fail without producing an ALI file; the process manager then skips
      --  this action, avoiding a spurious "data representation info
      --  unavailable" warning on top of the real error.
      Db.Add_Input (UID, Self.Lib_Ali_File, True);

      if not Db.Add_Output (UID, JSON_Out) then
         return False;
      end if;

      return True;
   end On_Tree_Insertion;

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
      pragma Unreferenced (Self, Status, Stdout);
   begin
      --  The wrapper prints to stderr when the compiler fails (a one-line
      --  warning) and, in verbose mode, also the full compiler output.
      --  Forward whatever was captured unless the user asked for quiet output.
      if Stderr /= Null_Unbounded_String and then not Configuration.Quiet then
         Standard.Ada.Text_IO.Put
           (Standard.Ada.Text_IO.Standard_Error, To_String (Stderr));
      end if;

      return True;
   end Post_Command;

   ---------
   -- UID --
   ---------

   overriding
   function UID (Self : Object) return Actions.Action_Id'Class is
   begin
      return Data_Rep.Create (Self.CU);
   end UID;

end GPR2.Build.Actions.Compile.Ada.Data_Rep;
