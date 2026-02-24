with GPR2.Build.Command_Line;
with GPR2.Build.Compilation_Unit;

package GPR2.Build.Actions.Compile.Ada.Global_Gen is

   type Global_Gen_Id is new GPR2.Build.Actions.Compile.Ada.Ada_Compile_Id
   with null record;

   overriding
   function Create
     (Src : GPR2.Build.Compilation_Unit.Object) return Global_Gen_Id;

   type Object is new GPR2.Build.Actions.Compile.Ada.Object with null record;

   overriding
   function UID (Self : Object) return GPR2.Build.Actions.Action_Id'Class;

   overriding
   function Action_Class (Self : Global_Gen_Id) return Value_Type
   is ("Global_Gen");

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
   procedure Initialize
     (Self : in out Object; Unit : GPR2.Build.Compilation_Unit.Object);

   overriding
   function Extended (Self : Object) return Object;

end GPR2.Build.Actions.Compile.Ada.Global_Gen;
