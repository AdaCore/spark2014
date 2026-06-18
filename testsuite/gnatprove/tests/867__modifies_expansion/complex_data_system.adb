pragma Ada_2022;

with Interfaces; use Interfaces;

--  This test verifies the translation of Modifies by calling subprograms
--  annotated with Modifies and checking that we can prove the same contract
--  expanded as a post. We use deep delta aggregates whenever possible.

procedure Complex_Data_System with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Driver_Profile is tagged record
      Version_ID : Natural := 1;
   end record;

   type Advanced_Optical_Profile is new Driver_Profile with record
      Frequency_Filter : Float := 550.0; -- nanometers
      Gain_Multiplier  : Positive := 2;
   end record;

   type Profile_Access is access Driver_Profile'Class;

   type Sample_Array is array (Positive range <>) of Integer;

   type Signal_History (Channel_Count : Positive) is record
      Samples      : Sample_Array (1 .. Channel_Count) := (others => 0);
      Average_Calc : Integer := 0;
   end record;

   type Operation_Mode is (Idle, Active, Diagnostic);

   type Sub_Processor (Mode : Operation_Mode := Idle) is record
      Cycles_Count : Natural := 0;
      case Mode is
         when Idle =>
            Low_Power_Saved : Boolean := True;
         when Active =>
            Telemetry_Buffer : Signal_History (Channel_Count => 4);
         when Diagnostic =>
            Error_Code       : Interfaces.Unsigned_32 := 0;
            Hardware_Override: Boolean := False;
      end case;
   end record;

   type Matrix_Coordinate is record
      Row : Positive;
      Col : Positive;
   end record;

   type Processor_Grid is array (1 .. 3, 1 .. 3) of Sub_Processor;

   type Metadata_Wrapper is record
      Last_Checked : Matrix_Coordinate := (Row => 1, Col => 1);
      Is_Reliable  : Boolean           := True;
   end record;

   type Sensor_Matrix_Node is record
      Grid             : Processor_Grid;
      Driver           : Profile_Access;
      Meta             : Metadata_Wrapper;
   end record;

   function L_Eq (X, Y : Driver_Profile'Class) return Boolean with
     Import,
     Global => null,
     Annotate => (GNATprove, Logical_Equal);

   function L_Eq (X, Y : Sensor_Matrix_Node) return Boolean with
     Import,
     Global => null,
     Annotate => (GNATprove, Logical_Equal);

   function Copy (X : Sensor_Matrix_Node) return Sensor_Matrix_Node with
     Import,
     Global => null,
     Post => L_Eq (X, Copy'Result);

   procedure Upgrade_To_Optical (Node         : in out Sensor_Matrix_Node;
                                 Upgrade_Flag : Boolean)
     with Modifies => (Node.Driver when Upgrade_Flag);

   procedure Upgrade_To_Optical (Node         : in out Sensor_Matrix_Node;
                                 Upgrade_Flag : Boolean)
   is
   begin
      if Upgrade_Flag then
         Node.Driver := new Advanced_Optical_Profile'
           (Version_ID       => 2,
            Frequency_Filter => 620.0,
            Gain_Multiplier  => 4);
      end if;
   end Upgrade_To_Optical;

   procedure Call_Upgrade_To_Optical
     (Node         : in out Sensor_Matrix_Node;
      Upgrade_Flag : Boolean)
     with Post =>
       (Static =>
          (if Upgrade_Flag
           then L_Eq (Node, (Copy (Node)'Old with delta Driver => Node.Driver))
           else L_Eq (Copy (Node)'Old, Node)));

   procedure Call_Upgrade_To_Optical
     (Node         : in out Sensor_Matrix_Node;
      Upgrade_Flag : Boolean)
   is
   begin
      Upgrade_To_Optical (Node, Upgrade_Flag);
   end Call_Upgrade_To_Optical;

   procedure Reset_Driver_Version (Node : in out Sensor_Matrix_Node) with
     Pre => Node.Driver /= null,
     Post =>
       (Static =>

          --  Expand equality as deep delta aggregates do not support
          --  dereferences for now.

          L_Eq (Node, (Copy (Node)'Old with delta Driver => Node.Driver))
            and then Node.Driver /= null
            and then L_Eq (Node.Driver.all, (Copy (Node)'Old.Driver.all with delta
                Version_Id => Node.Driver.Version_ID)));

   procedure Reset_Driver_Version (Node : in out Sensor_Matrix_Node)
   is
   begin
      Node.Driver.Version_ID := 1;
   end Reset_Driver_Version;

   procedure Call_Reset_Driver_Version (Node : in out Sensor_Matrix_Node) with
     Pre => Node.Driver /= null,
     Modifies => Node.Driver.all.Version_ID;

   procedure Call_Reset_Driver_Version (Node : in out Sensor_Matrix_Node)
   is
   begin
      Reset_Driver_Version (Node);
   end Call_Reset_Driver_Version;

   procedure Activate_Diagnostic_Mode
     (Node           : in out Sensor_Matrix_Node;
      Fault_Detected : Boolean)
     with Modifies => (Node.Grid(3, 3) when Fault_Detected);

   procedure Activate_Diagnostic_Mode
     (Node           : in out Sensor_Matrix_Node;
      Fault_Detected : Boolean)
   is
   begin
      if Fault_Detected then
         Node.Grid(3, 3) :=
           (Mode              => Diagnostic,
            Cycles_Count      => 0,
            Error_Code        => 0,
            Hardware_Override => True);
      end if;
   end Activate_Diagnostic_Mode;

   procedure Call_Activate_Diagnostic_Mode
     (Node           : in out Sensor_Matrix_Node;
      Fault_Detected : Boolean)
     with Post =>
       (Static =>
          (if Fault_Detected

           --  Expand equality as deep delta aggregates do not support
           --  multidimensional arrays for now.

           then L_Eq (Node, (Copy (Node)'Old with delta Grid => Node.Grid))
             and then Node.Grid (1, 1) = Node.Grid (1, 1)'Old
             and then Node.Grid (1, 2) = Node.Grid (1, 2)'Old
             and then Node.Grid (1, 3) = Node.Grid (1, 3)'Old
             and then Node.Grid (2, 1) = Node.Grid (2, 1)'Old
             and then Node.Grid (2, 2) = Node.Grid (2, 2)'Old
             and then Node.Grid (2, 3) = Node.Grid (2, 3)'Old
             and then Node.Grid (3, 1) = Node.Grid (3, 1)'Old
             and then Node.Grid (3, 2) = Node.Grid (3, 2)'Old
           else L_Eq (Copy (Node)'Old, Node)));

   procedure Call_Activate_Diagnostic_Mode
     (Node           : in out Sensor_Matrix_Node;
      Fault_Detected : Boolean)
   is
   begin
      Activate_Diagnostic_Mode (Node, Fault_Detected);
   end Call_Activate_Diagnostic_Mode;

   procedure Activate_Diagnostic_Mode_2
     (Node           : in out Sensor_Matrix_Node;
      Fault_Detected : Boolean)
     with Modifies =>
       (Node.Grid(3, 3) when Fault_Detected,
        (Node.Grid(1, 1).Cycles_Count, Node.Grid(2, 2).Cycles_Count));

   procedure Activate_Diagnostic_Mode_2
     (Node           : in out Sensor_Matrix_Node;
      Fault_Detected : Boolean)
   is
   begin
      if Fault_Detected then
         Node.Grid(3, 3) :=
           (Mode              => Diagnostic,
            Cycles_Count      => 0,
            Error_Code        => 0,
            Hardware_Override => True);
      end if;
      Node.Grid(1, 1).Cycles_Count := 0;
      Node.Grid(2, 2).Cycles_Count := 0;
   end Activate_Diagnostic_Mode_2;

   procedure Call_Activate_Diagnostic_Mode_2
     (Node           : in out Sensor_Matrix_Node;
      Fault_Detected : Boolean)
     with Post =>
       (Static =>

           --  Expand equality as deep delta aggregates do not support
           --  multidimensional arrays for now.

           L_Eq (Node, (Copy (Node)'Old with delta Grid => Node.Grid))
             and then Node.Grid (1, 1) =
              (Node.Grid (1, 1)'Old with delta
                  Cycles_Count => Node.Grid (1, 1).Cycles_Count)
             and then Node.Grid (1, 2) = Node.Grid (1, 2)'Old
             and then Node.Grid (1, 3) = Node.Grid (1, 3)'Old
             and then Node.Grid (2, 1) = Node.Grid (2, 1)'Old
             and then Node.Grid (2, 2) =
              (Node.Grid (2, 2)'Old with delta
                  Cycles_Count => Node.Grid (2, 2).Cycles_Count)
             and then Node.Grid (2, 3) = Node.Grid (2, 3)'Old
             and then Node.Grid (3, 1) = Node.Grid (3, 1)'Old
             and then Node.Grid (3, 2) = Node.Grid (3, 2)'Old
             and then (if not Fault_Detected then Node.Grid (3, 3) = Node.Grid (3, 3)'Old));

   procedure Call_Activate_Diagnostic_Mode_2
     (Node           : in out Sensor_Matrix_Node;
      Fault_Detected : Boolean)
   is
   begin
      Activate_Diagnostic_Mode_2 (Node, Fault_Detected);
   end Call_Activate_Diagnostic_Mode_2;

   procedure Record_System_Sample (Node      : in out Sensor_Matrix_Node;
                                   Val       : Integer;
                                   Log_Event : Boolean)
     with
       Pre => Node.Grid(2, 2).Mode = Active,
       Modifies => (Node.Grid(2, 2).Telemetry_Buffer.Samples,
                    Node.Meta when Log_Event);

   procedure Record_System_Sample (Node      : in out Sensor_Matrix_Node;
                                   Val       : Integer;
                                   Log_Event : Boolean)
   is
   begin
      Node.Grid(2, 2).Telemetry_Buffer.Samples(1) := Val;

      if Log_Event then
         Node.Meta.Last_Checked := (Row => 2, Col => 2);
         Node.Meta.Is_Reliable  := True;
      end if;
   end Record_System_Sample;

   procedure Call_Record_System_Sample (Node      : in out Sensor_Matrix_Node;
                                   Val       : Integer;
                                   Log_Event : Boolean)
     with
       Pre => Node.Grid(2, 2).Mode = Active,
       Modifies => (Node.Grid(2, 2).Telemetry_Buffer.Samples,
                    Node.Meta when Log_Event);

   procedure Call_Record_System_Sample (Node      : in out Sensor_Matrix_Node;
                                   Val       : Integer;
                                   Log_Event : Boolean)
   is
   begin
      Record_System_Sample (Node, Val, Log_Event);
   end Call_Record_System_Sample;

begin
   null;
end Complex_Data_System;
