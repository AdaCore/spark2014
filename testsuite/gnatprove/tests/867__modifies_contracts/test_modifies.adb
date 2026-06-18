procedure Test_Modifies with SPARK_Mode is

   --  Handling of refined post: modifies is checked before the cut and assumed
   --  to check the postcondition.

   package Test_Refined is
      procedure Reset_Y (X, Y : in out Integer) with
        Modifies => Y, --  @MODIFIES:PASS
        Post => X = X'Old; --  @POSTCONDITION:PASS

      procedure Reset_Y_Bad (X, Y : in out Integer) with
        Modifies => Y, --  @MODIFIES:FAIL
        Post => X = X'Old; --  @POSTCONDITION:PASS
   end Test_Refined;

   package body Test_Refined is
      procedure Reset_Y (X, Y : in out Integer) with
        Refined_Post => Y = 8
      is
      begin
         Y := 8;
      end Reset_Y;

      procedure Reset_Y_Bad (X, Y : in out Integer) with
        Refined_Post => Y = 8
      is
      begin
         Y := 8;
         X := 1;
      end Reset_Y_Bad;
   end Test_Refined;

   --  Handling of abstract states: test both private and visible state
   --  abstraction.

   package Nested with Abstract_State => State is
      package Off with Abstract_State => State_2 is
         procedure P with Global => (Output => State_2);
      end Off;
      procedure P with Modifies => State;
   end Nested;

   package body Nested with Refined_State => (State => (X, Y)) is
      X, Y : Integer;
      procedure P is
      begin
         X := 34;
         Y := 10;
      end P;
      package body Off with SPARK_Mode => Off is
         procedure P is null;
      end Off;
   end Nested;

   package Hidden_State is
      procedure P;
   end Hidden_State;

   package body Hidden_State with SPARK_Mode => Off is
      X : Integer; --  Hidden state
      procedure P is
      begin
         X := X / 2;
      end P;
   end Hidden_State;

   procedure Reset_State (B1, B2 : Boolean) with
     Global => (In_Out => (Nested.State, Nested.Off.State_2)),
     Modifies => --  @MODIFIES:PASS
       (Nested.State when B1,
        (Nested.State, Nested.Off.State_2) when B2)
   is
   begin
      if B1 or B2 then
         Nested.P;
      end if;
      if B2 then
         Nested.Off.P;
      end if;
   end Reset_State;

   procedure Reset_State_Bad_1 (B1, B2 : Boolean) with
     Global => (In_Out => (Nested.State, Nested.Off.State_2)),
     Modifies => --  @MODIFIES:FAIL
       (Nested.State when B1,
        (Nested.State, Nested.Off.State_2) when B2)
   is
   begin
      if B1 or B2 then
         Nested.P;
      end if;
      if B2 or B1 then
         Nested.Off.P;
      end if;
   end Reset_State_Bad_1;

   procedure Reset_State_Bad_2 (B1, B2 : Boolean) with
     Global => (In_Out => (Nested.State, Nested.Off.State_2)),
     Modifies => --  @MODIFIES:FAIL
       (Nested.State when B1,
        (Nested.State, Nested.Off.State_2) when B2)
   is
   begin
      Nested.P;
      if B2 then
         Nested.Off.P;
      end if;
   end Reset_State_Bad_2;

   --  Handling of hidden state, use entity names to report failed checks
   --  The hidden state Hidden_State.X has been forgotten, proof should complain

   procedure Forgotten_State (B : Boolean) with
     Modifies => (Nested.State, Nested.Off.State_2 when B); --  @MODIFIES:FAIL

   procedure Forgotten_State (B : Boolean) is
   begin
      Nested.P;
      if B then
         Nested.Off.P;
      end if;
      Hidden_State.P;
   end Forgotten_State;

   --  Nested records

   type Inner_Record is record
      Field_A : Integer;
      Field_B : Integer;
   end record;

   type Outer_Record is record
      Left_Branch  : Inner_Record;
      Right_Branch : Inner_Record;
   end record;

   procedure Modify_Left_A (Obj : in out Outer_Record) with
     Modifies => Obj.Left_Branch.Field_A; -- @MODIFIES:PASS

   procedure Modify_Left_A (Obj : in out Outer_Record) is
   begin
      Obj.Left_Branch.Field_A := 42;
   end Modify_Left_A;

   procedure Modify_Left_A_And_B (B : Boolean; Obj : in out Outer_Record) with
     Modifies => (Obj.Left_Branch.Field_A, Obj.Left_Branch.Field_A when B); -- @MODIFIES:FAIL

   procedure Modify_Left_A_And_B (B : Boolean; Obj : in out Outer_Record) is
   begin
      Obj.Left_Branch.Field_A := 42;
      if B then
         Obj.Left_Branch.Field_B := 42;
      end if;
   end Modify_Left_A_And_B;

   procedure Modify_Left_A_Bad (B1, B2 : Boolean; Obj : in out Outer_Record) with
     Modifies => (Obj.Left_Branch.Field_A when B1, Obj when B2); -- @MODIFIES:FAIL

   procedure Modify_Left_A_Bad (B1, B2 : Boolean; Obj : in out Outer_Record) is
   begin
      Obj.Left_Branch.Field_A := 42;
      if B2 then
         Obj.Left_Branch.Field_B := 42;
      end if;
   end Modify_Left_A_Bad;

   --  Mutable discriminants

   type Buffer_Kind is (Idling, Processing);

   type Dynamic_Buffer (State : Buffer_Kind := Idling) is record
      Data_Payload : Integer;
      case State is
         when Idling =>
            Idle_Counter : Natural;
         when Processing =>
            Valid_Flag   : Boolean;
      end case;
   end record;

   procedure Update_Payload (B : Boolean; Buf : in out Dynamic_Buffer) with
     Pre => not Buf'Constrained ,
     Modifies => (Buf.Data_Payload when B, Buf when not B); -- @MODIFIES:PASS

   procedure Update_Payload (B : Boolean; Buf : in out Dynamic_Buffer) is
   begin
      if B then
         Buf.Data_Payload := 100;
      else
         Buf := (State => Idling, Data_Payload => 30, Idle_Counter => 0);
      end if;
   end Update_Payload;

   procedure Update_Payload_Bad (B : Boolean; Buf : in out Dynamic_Buffer) with
     Pre => not Buf'Constrained,
     Modifies => Buf.Data_Payload; -- @MODIFIES:FAIL

   procedure Update_Payload_Bad (B : Boolean; Buf : in out Dynamic_Buffer) is
   begin
      if B then
         Buf.Data_Payload := 100;
      else
         Buf := (State => Idling, Data_Payload => 30, Idle_Counter => 0);
      end if;
   end Update_Payload_Bad;

   -- Tagged types

   package Tagged_Types is
      type Base_Device is tagged record
         Power_On : Boolean;
      end record;

      procedure P (X : in out Base_Device) with
        Import, Global => null, Always_Terminates;

      type Smart_Device is new Base_Device with record
         Frequency_Khz : Positive;
      end record;

      procedure P (X : in out Smart_Device) with
        Import, Global => null, Always_Terminates;
   end Tagged_Types;
   use Tagged_Types;

   procedure Toggle_Power (D : in out Base_Device) with
     Modifies => D.Power_On; -- @MODIFIES:PASS

   procedure Toggle_Power (D : in out Base_Device) is
   begin
      P (D);
   end Toggle_Power;

   procedure Toggle_Power_Bad (D : in out Base_Device) with
     Extensions_Visible,
     Modifies => D.Power_On; -- @MODIFIES:FAIL

   procedure Toggle_Power_Bad (D : in out Base_Device) is
   begin
      P (Base_Device'Class (D));
   end Toggle_Power_Bad;

   --  Test with an array

   type Schedule is array (1 .. 10) of Boolean;

   type Worker is record
      Timeline   : Schedule;
      Current_Id : Positive;
   end record;

   procedure Advance_And_Clear (W : in out Worker) with
     Pre => W.Current_Id in 1 .. 10,
     Modifies => (W.Timeline (W.Current_Id), W.Current_Id); -- @MODIFIES:PASS

   procedure Advance_And_Clear (W : in out Worker) is
   begin
      W.Timeline (W.Current_Id) := False;
      W.Current_Id := W.Current_Id + 1;
   end Advance_And_Clear;

   procedure Advance_And_Clear_2 (W : in out Worker) with
     Modifies => (W.Timeline (W.Current_Id), W.Current_Id when W.Current_Id < 9); -- @MODIFIES:PASS

   procedure Advance_And_Clear_2 (W : in out Worker) is
   begin
      W.Timeline (W.Current_Id) := False;
      if W.Current_Id < 9 then
         W.Current_Id := W.Current_Id + 1;
      end if;
   end Advance_And_Clear_2;

   procedure Advance_And_Clear_Bad (W : in out Worker) with
     Pre => W.Current_Id in 1 .. 9,
     Modifies => (W.Timeline (W.Current_Id), W.Current_Id); -- @MODIFIES:FAIL

   procedure Advance_And_Clear_Bad (W : in out Worker) is
   begin
      W.Current_Id := W.Current_Id + 1;
      W.Timeline (W.Current_Id) := False;
   end Advance_And_Clear_Bad;

   procedure Clear (W : in out Worker) with
     Modifies => -- @MODIFIES:PASS
       (W.Timeline (W.Current_Id) when W.Current_Id in 1 .. 10,
        W.Timeline when W.Current_Id not in 1 .. 10);

   procedure Clear (W : in out Worker) is
   begin
      if W.Current_Id in 1 .. 10 then
         W.Timeline (W.Current_Id) := False;
         else
         W.Timeline := (others => False);
      end if;
   end Clear;

   --  Multidimensional

   type Grid is array (1 .. 3, 1 .. 3) of Integer;

   type Board is record
      Matrix : Grid;
   end record;

   procedure Update_Cell (B : in out Board; Row : Positive) with
     Pre => Row in 1 .. 3,
     Modifies => (B.Matrix (Row, 2)); -- @MODIFIES:PASS

   procedure Update_Cell (B : in out Board; Row : Positive) is
   begin
      B.Matrix (Row, 2) := 99;
   end Update_Cell;

   --  Test with an access type

   type Node is record
      Value : Integer;
      Count : Integer;
   end record;

   type Node_Access is access Node;

   type Engine_State is record
      Primary_Node : Node_Access;
      Backup_Node  : Node_Access;
   end record;

   procedure Update_Primary_Value (State : in out Engine_State) with
     Pre => State.Primary_Node /= null,
     Modifies => State.Primary_Node.all; -- @MODIFIES:PASS

   procedure Update_Primary_Value (State : in out Engine_State) is
   begin
      State.Primary_Node.Value := 100;
   end Update_Primary_Value;

   procedure Update_Primary_Value_2 (State : in out Engine_State; Reset_Count : Boolean) with
     Pre => State.Primary_Node /= null,
     Modifies => (State.Primary_Node when Reset_Count, State.Primary_Node.all.Value); -- @MODIFIES:PASS

   procedure Update_Primary_Value_2 (State : in out Engine_State; Reset_Count : Boolean) is
   begin
      State.Primary_Node.Value := 100;
      if Reset_Count then
         State.Primary_Node.Count := 0;
      end if;
   end Update_Primary_Value_2;

   procedure Update_Primary_Value_Bad (State : in out Engine_State) with
     Pre => State.Primary_Node /= null,
     Modifies => (State.Primary_Node.all, State.Backup_Node.all); -- @MODIFIES:FAIL

   procedure Update_Primary_Value_Bad (State : in out Engine_State) is
   begin
      State.Backup_Node := State.Primary_Node;
      State.Primary_Node := new Node'(Value => 13, Count => 0);
   end Update_Primary_Value_Bad;

   procedure Update_Primary_Value_Bad_2 (State : in out Engine_State) with
     Pre => State.Primary_Node /= null and State.Backup_Node /= null,
     Modifies => State.Primary_Node.all; -- @MODIFIES:FAIL

   procedure Update_Primary_Value_Bad_2 (State : in out Engine_State) is
   begin
      State.Backup_Node.Value := State.Primary_Node.Value;
      State.Primary_Node.Value := 100;
   end Update_Primary_Value_Bad_2;

   --  Access to an unconstrained array

   type Dynamic_Vector is array (Positive range <>) of Integer;
   type Vector_Access is access Dynamic_Vector;

   type Memory_Manager is record
      Buffer : Vector_Access;
      Active : Boolean;
   end record;

   procedure Resize_Buffer (Manager : in out Memory_Manager) with
     Modifies => Manager.Buffer; -- @MODIFIES:PASS

   procedure Resize_Buffer (Manager : in out Memory_Manager) is
   begin
      Manager.Buffer := new Dynamic_Vector'(1 .. 10 => 0);
   end Resize_Buffer;

   procedure Resize_Buffer_Bad (Manager : in out Memory_Manager) with
     Pre => Manager.Buffer /= null and then 3 in Manager.Buffer'Range,
     Modifies => Manager.Buffer.all (3); -- @MODIFIES:FAIL

   procedure Resize_Buffer_Bad (Manager : in out Memory_Manager) is
   begin
      Manager.Buffer (1) := 0;
   end Resize_Buffer_Bad;

   procedure In_Place_Resize_Violation (Manager : in out Memory_Manager) with
     Pre => Manager.Buffer /= null,
     Modifies => Manager.Buffer.all; -- @MODIFIES:PASS

   procedure In_Place_Resize_Violation (Manager : in out Memory_Manager) is
   begin
      Manager.Buffer := new Dynamic_Vector'(1 .. 10 => 0);
   end In_Place_Resize_Violation;

   -- Access to classwide type

   type Element is tagged record
      ID : Natural;
   end record;

   type Numeric_Element is new Element with record
      Val : Integer;
   end record;

   type Text_Element is new Element with record
      Len : Positive;
   end record;

   type Element_Ptr is access all Element'Class;

   type Elt_Node is record
      Payload : Element_Ptr;
      Visited : Boolean;
   end record;

   procedure Mutate_To_Text (N : in out Elt_Node) with
     Modifies => N.Payload; -- @MODIFIES:PASS

   procedure Mutate_Tag_Violation (N : in out Elt_Node) with
     Modifies => N.Payload.all; -- @MODIFIES:PASS

   procedure Mutate_To_Text (N : in out Elt_Node) is
   begin
      N.Payload := new Text_Element'(ID => 1, Len => 32);
   end Mutate_To_Text;

   procedure Mutate_Tag_Violation (N : in out Elt_Node) is
   begin
      N.Payload := new Text_Element'(ID => 2, Len => 64);
   end Mutate_Tag_Violation;

   --  Access to type with discriminants

   type Vector_Holder (Last : Natural) is record
      V : Dynamic_Vector (1 .. Last);
   end record;
   type Holder_Access is access Vector_Holder;

   type Memory_Manager_2 is record
      Buffer : Holder_Access;
      Active : Boolean;
   end record;

   procedure Resize_Buffer (Manager : in out Memory_Manager_2) with
     Modifies => Manager.Buffer; -- @MODIFIES:PASS

   procedure Resize_Buffer (Manager : in out Memory_Manager_2) is
   begin
      Manager.Buffer := new Vector_Holder'(10, (1 .. 10 => 0));
   end Resize_Buffer;

   procedure Resize_Buffer_Bad (Manager : in out Memory_Manager_2) with
     Pre => Manager.Buffer /= null and then Manager.Buffer.Last = 3,
     Modifies => Manager.Buffer.all.V (3); -- @MODIFIES:FAIL

   procedure Resize_Buffer_Bad (Manager : in out Memory_Manager_2) is
   begin
      Manager.Buffer.V (2) := 0;
   end Resize_Buffer_Bad;

   procedure In_Place_Resize_Violation (Manager : in out Memory_Manager_2) with
     Pre => Manager.Buffer /= null,
     Modifies => Manager.Buffer.all; -- @MODIFIES:PASS

   procedure In_Place_Resize_Violation (Manager : in out Memory_Manager_2) is
   begin
      Manager.Buffer := new Vector_Holder'(10, (1 .. 10 => 0));
   end In_Place_Resize_Violation;

begin
   null;
end;
