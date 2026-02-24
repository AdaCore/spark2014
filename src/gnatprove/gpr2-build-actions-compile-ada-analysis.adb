with Configuration; use Configuration;
with GPR2.Build.Artifacts.Source_Files;
with GPR2.Project.Attribute;
with GPR2.Project.Registry.Attribute;

package body GPR2.Build.Actions.Compile.Ada.Analysis is

   package PRA renames GPR2.Project.Registry.Attribute;

   function Artifacts_Base_Name
     (Unit : GPR2.Build.Compilation_Unit.Object) return Simple_Name;
   --  ??? copied from gpr2-build-actions-compile-ada.adb

   function Get_Attr
     (V       : GPR2.Project.View.Object;
      Name    : Q_Attribute_Id;
      Idx     : Language_Id;
      Default : Value_Type) return Value_Type;
   --  ??? copied from gpr2-build-actions-compile-ada.adb

   -------------------------
   -- Artifacts_Base_Name --
   -------------------------

   function Artifacts_Base_Name
     (Unit : GPR2.Build.Compilation_Unit.Object) return Simple_Name
   is
      Main : constant Compilation_Unit.Unit_Location := Unit.Main_Part;
      BN   : constant Simple_Name := Simple_Name (Main.Source.Base_Name);

   begin
      if Main.Index = No_Index then
         return BN;
      else
         declare
            Img : constant String := Main.Index'Image;
            Sep : constant String :=
              Get_Attr
                (Main.View,
                 PRA.Compiler.Multi_Unit_Object_Separator,
                 Ada_Language,
                 "~");
         begin
            return BN & Simple_Name (Sep & Img (Img'First + 1 .. Img'Last));
         end;
      end if;
   end Artifacts_Base_Name;

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
      --  ??? We are not supposed to create temp files if Signature_Only is
      --  false, but we can't know the file name without creating it.
      declare
         Opt_File : constant String :=
           Configuration.Get_Or_Create_Unit_Opt_File
             (Self.CU,
              True,
              String (Self.CU.Owning_View.Object_Directory.Value),
              String
                (Configuration.Artifact_Dir (Self.CU.Owning_View.Tree).Value));
      begin
         Cmd_Line.Add_Argument ("-gnates=" & Opt_File);
      end;

      --  object path file
      Cmd_Line.Add_Argument ("-gnateO=" & To_String (Self.Object_Path_File));

      for Arg of Configuration.CL_Switches.Cargs_List loop
         Cmd_Line.Add_Argument (Arg);
      end loop;
   end Compute_Command;

   -----------------------
   -- Compute_Signature --
   -----------------------

   overriding
   procedure Compute_Signature
     (Self : in out Object; Check_Checksums : Boolean) is
   begin
      GPR2.Build.Actions.Compile.Ada.Object (Self).Compute_Signature
        (Check_Checksums);

      for ALI_File of Self.ALI_Files loop
         if not Self.Signature.Add_Input (ALI_File, Check_Checksums) then
            return;
         end if;
      end loop;
   end Compute_Signature;

   function Create
     (Src : GPR2.Build.Compilation_Unit.Object) return Analysis_Id is
   begin
      return
        (GPR2.Build.Actions.Compile.Ada.Ada_Compile_Id'(Ada.Create (Src))
         with null record);
   end Create;

   procedure Initialize
     (Self             : in out Object;
      Unit             : GPR2.Build.Compilation_Unit.Object;
      Object_Path_File : String;
      Deps             : GPR2.Build.Compilation_Unit.Maps.Map)
   is

      function ALI_For_Unit
        (CU : GPR2.Build.Compilation_Unit.Object) return GPR2.Path_Name.Object;

      function ALI_For_Unit
        (CU : GPR2.Build.Compilation_Unit.Object) return GPR2.Path_Name.Object
      is
      begin
         return
           CU.Owning_View.Object_Directory.Compose
             (Artifacts_Base_Name (CU) & ".ali");
      end ALI_For_Unit;

   begin
      GPR2.Build.Actions.Compile.Ada.Object (Self).Initialize (Unit);
      Self.Object_Path_File := To_Unbounded_String (Object_Path_File);
      Self.Obj_File :=
        Build.Artifacts.Object_File.Create
          (Self.View.Object_Directory.Compose
             (Artifacts_Base_Name (Unit) & ".spark"));
      Self.ALI_Files.Insert
        (GPR2.Build.Artifacts.Files.Create (ALI_For_Unit (Self.CU)));
      for Dep of Deps loop
         if Dep.Is_Defined then
            --  we use Include here even though the deps should not contain
            --  duplicates, as they might contain the unit itself, for which
            --  we already added the ALI file.
            Self.ALI_Files.Include
              (GPR2.Build.Artifacts.Files.Create (ALI_For_Unit (Dep)));
         end if;

      end loop;
   end Initialize;

   --------------
   -- Extended --
   --------------

   overriding
   function Extended (Self : Object) return Object is
   begin
      return Result : Object := Self do
         Result.Object_Path_File := Null_Unbounded_String;
         Result.ALI_Files := File_Sets.Empty;
      end return;
   end Extended;

   --------------
   -- Get_Attr --
   --------------

   function Get_Attr
     (V       : GPR2.Project.View.Object;
      Name    : Q_Attribute_Id;
      Idx     : Language_Id;
      Default : Value_Type) return Value_Type
   is
      Attr : constant GPR2.Project.Attribute.Object :=
        V.Attribute (Name, PAI.Create (Idx));
   begin
      if Attr.Is_Defined then
         return Attr.Value.Text;
      else
         return Default;
      end if;
   end Get_Attr;

   -----------------------
   -- On_Tree_Insertion --
   -----------------------

   overriding
   function On_Tree_Insertion
     (Self : Object; Db : in out GPR2.Build.Tree_Db.Object) return Boolean
   is
      UID : constant Actions.Action_Id'Class := Object'Class (Self).UID;
   begin
      Db.Add_Input
        (UID,
         GPR2.Build.Artifacts.Source_Files.Create (Self.Src.Path_Name),
         True);

      for ALI_File of Self.ALI_Files loop
         Db.Add_Input (Self.UID, ALI_File, True);
      end loop;

      if Self.Obj_File.Is_Defined
        and then not Db.Add_Output (UID, Self.Obj_File)
      then
         return False;
      end if;

      return True;
   end On_Tree_Insertion;

   overriding
   function UID (Self : Object) return Actions.Action_Id'Class is
   begin
      return Analysis.Create (Self.CU);
   end UID;

   --------------------
   -- On_Ready_State --
   --------------------

   overriding
   function On_Ready_State (Self : in out Object) return Boolean is
      pragma Unreferenced (Self);
   begin
      return True;
   end On_Ready_State;

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
      pragma Unreferenced (Self, Status, Stdout, Stderr);

   begin
      return True;
   end Post_Command;

end GPR2.Build.Actions.Compile.Ada.Analysis;
