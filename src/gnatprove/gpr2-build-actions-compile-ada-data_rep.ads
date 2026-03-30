with GPR2.Build.Command_Line;
with GPR2.Build.Compilation_Unit;
with GPR2.Build.Tree_Db;

package GPR2.Build.Actions.Compile.Ada.Data_Rep is

   type Data_Rep_Id is new GPR2.Build.Actions.Compile.Ada.Ada_Compile_Id
   with null record;

   overriding
   function Create
     (Src : GPR2.Build.Compilation_Unit.Object) return Data_Rep_Id;

   overriding
   function Action_Class (Self : Data_Rep_Id) return Value_Type
   is ("Data_Rep");

   type Object is new GPR2.Build.Actions.Compile.Ada.Object with null record;

   overriding
   function UID (Self : Object) return GPR2.Build.Actions.Action_Id'Class;

   overriding
   procedure Compute_Command
     (Self           : in out Object;
      Slot           : Positive;
      Cmd_Line       : in out GPR2.Build.Command_Line.Object;
      Signature_Only : Boolean);

   overriding
   function Post_Command
     (Self   : in out Object;
      Status : Execution_Status;
      Stdout : Unbounded_String := Null_Unbounded_String;
      Stderr : Unbounded_String := Null_Unbounded_String) return Boolean;

   function Applicable
     (CU : GPR2.Build.Compilation_Unit.Object) return Boolean;
   --  Return True when a data-representation action should be generated for
   --  CU: the analysis mode includes data representation, no target
   --  representation file is provided, and the source file contains a single
   --  unit.

   procedure Initialize
     (Self : in out Object; Unit : GPR2.Build.Compilation_Unit.Object);
   --  Initialize the action for the given compilation unit

   function Data_Rep_File_For_Unit
     (CU : GPR2.Build.Compilation_Unit.Object)
      return GPR2.Build.Artifacts.Files.Object;
   --  Return the JSON artifact path for the given compilation unit

   function JSON_Output
     (Self : Object) return GPR2.Build.Artifacts.Files.Object;
   --  Return the JSON artifact produced by this action

   overriding
   function On_Tree_Insertion
     (Self : Object; Db : in out GPR2.Build.Tree_Db.Object) return Boolean;

   overriding
   function Extended (Self : Object) return Object;

   overriding
   function Display_Output (Action : Object) return Boolean
   is (False);
   --  Suppress output for data rep actions

end GPR2.Build.Actions.Compile.Ada.Data_Rep;
