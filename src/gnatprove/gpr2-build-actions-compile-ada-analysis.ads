with GPR2.Build.Command_Line;
with GPR2.Build.Compilation_Unit;
with GPR2.Build.Compilation_Unit.Maps;

package GPR2.Build.Actions.Compile.Ada.Analysis is

   package File_Sets is new
     Standard.Ada.Containers.Hashed_Sets
       (Artifacts.Files.Object,
        Artifacts.Files.Hash,
        Artifacts.Files."=",
        Artifacts.Files."=");

   type Analysis_Id is new GPR2.Build.Actions.Compile.Ada.Ada_Compile_Id
   with null record;

   overriding
   function Create
     (Src : GPR2.Build.Compilation_Unit.Object) return Analysis_Id;

   type Object is new GPR2.Build.Actions.Compile.Ada.Object with record
      Object_Path_File : Unbounded_String;
      ALI_Files        : File_Sets.Set;
   end record;

   overriding
   function UID (Self : Object) return GPR2.Build.Actions.Action_Id'Class;

   function Action_Class (Self : Analysis_Id) return Value_Type
   is ("Analysis");

   overriding
   procedure Compute_Command
     (Self           : in out Object;
      Slot           : Positive;
      Cmd_Line       : in out GPR2.Build.Command_Line.Object;
      Signature_Only : Boolean);

   overriding
   procedure Compute_Signature
     (Self : in out Object; Check_Checksums : Boolean);

   overriding
   function On_Ready_State (Self : in out Object) return Boolean;

   procedure Initialize
     (Self             : in out Object;
      Unit             : GPR2.Build.Compilation_Unit.Object;
      Object_Path_File : String;
      Deps             : GPR2.Build.Compilation_Unit.Maps.Map);
   --  Initialize the analysis action for the given compilation unit.
   --  The Object_Path_File is the location of the file that contains all
   --  Object paths. The Deps is the set of unit dependencies, used to
   --  calculate the ALI files that are inputs to this action.

   overriding
   function On_Tree_Insertion
     (Self : Object; Db : in out GPR2.Build.Tree_Db.Object) return Boolean;

   overriding
   function Extended (Self : Object) return Object;

   overriding
   function Post_Command
     (Self   : in out Object;
      Status : Execution_Status;
      Stdout : Unbounded_String := Null_Unbounded_String;
      Stderr : Unbounded_String := Null_Unbounded_String) return Boolean;

end GPR2.Build.Actions.Compile.Ada.Analysis;
