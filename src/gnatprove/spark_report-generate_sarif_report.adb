with Ada.Directories;
with SARIF.Types;             use SARIF.Types;
with SARIF.Types.Outputs;
with VC_Kinds;                use VC_Kinds;
with VSS.JSON.Push_Writers;
with VSS.Strings;
with VSS.Strings.Conversions; use VSS.Strings.Conversions;
with VSS.Text_Streams.File_Output;

separate (SPARK_Report)
--!format off
procedure Generate_SARIF_Report (Filename : String; Info : JSON_Value)
--!format on
is
   Root       : SARIF.Types.Root;
   My_Run     : run;
   My_Results : SARIF.Types.result_Vector;

   Output : aliased VSS.Text_Streams.File_Output.File_Output_Text_Stream;
   Writer : VSS.JSON.Push_Writers.JSON_Simple_Push_Writer;

   function Tool_Invocation return SARIF.Types.invocation;
   function Rules return SARIF.Types.reportingDescriptor_Vector;
   --  Helper functions that generate subsections of the SARIF report

   function Mk_Multi_Message_String
     (S : String) return Optional_multiformatMessageString;
   --  Helper to create a multiformatMessageString object from a simple String

   procedure Handle_SPARK_Files;
   --  Parse all .spark files

   procedure Handle_SPARK_File (Fn : String);
   --  Parse and extract all information from a single SPARK file.

   procedure Handle_Source_Dir (Dir : String);
   --  Parse all .spark files in the given directory

   procedure Handle_Items (V : JSON_Array);

   function Location (V : JSON_Value) return SARIF.Types.location;
   --  Produce a SARIF location object from a JSON item that has "file",
   --  "line", "col" fields. "entity" field is optional and is added as a
   --  "logical" location.

   function Locations (V : JSON_Value) return SARIF.Types.location_Vector;
   --  Wrapper for Location that produces a vector

   function Message (V : JSON_Value) return SARIF.Types.message;
   --  Produce a SARIF message from a message object

   function SARIF_Location (V : JSON_Value) return SARIF.Types.location;
   --  Copy a SARIF location from JSON to sarif-ada

   function Severity_To_Result_Kind
     (S : String) return SARIF.Types.Enum.result_kind;
   --  Map result severity to SARIF result kind
   function Severity_To_Result_Level
     (S : String) return SARIF.Types.Enum.result_level;
   --  Map result severity to SARIF result level

   ------------------
   -- Handle_Items --
   ------------------

   procedure Handle_Items (V : JSON_Array) is
   begin
      for Index in 1 .. Length (V) loop
         declare
            Result       : constant JSON_Value := Get (V, Index);
            Severity     : constant String := Get (Get (Result, "severity"));
            Rule_Id      : constant String := Get (Get (Result, "rule"));
            Suppressions : SARIF.Types.suppression_Vector;
            Rel_Locs     : SARIF.Types.location_Vector;
         begin
            if Has_Field (Result, "suppressed") then
               declare
                  Suppr_Object : SARIF.Types.suppression :=
                    SARIF.Types.suppression'
                      (kind => SARIF.Types.Enum.external, others => <>);
                  Reason       : constant String :=
                    Get (Get (Result, "suppressed"));
               begin
                  if Reason /= "" then
                     Suppr_Object.justification := To_Virtual_String (Reason);
                  end if;
                  Suppressions.Append (Suppr_Object);
               end;
            end if;

            if Has_Field (Result, "relatedLocations") then
               declare
                  Locs : constant JSON_Array :=
                    Get (Result, "relatedLocations");
               begin
                  for Index in 1 .. Length (Locs) loop
                     Rel_Locs.Append (SARIF_Location (Get (Locs, Index)));
                  end loop;
               end;
            end if;

            My_Results.Append
              (SARIF.Types.result'
                 (ruleId           => To_Virtual_String (Rule_Id),
                  kind             =>
                    (True, Severity_To_Result_Kind (Severity)),
                  level            =>
                    (True, Severity_To_Result_Level (Severity)),
                  message          => Message (Get (Result, "message")),
                  suppressions     => Suppressions,
                  locations        => Locations (Result),
                  relatedLocations => Rel_Locs,
                  others           => <>));
         end;
      end loop;
   end Handle_Items;

   -----------------------
   -- Handle_Source_Dir --
   -----------------------

   procedure Handle_Source_Dir (Dir : String) is

      procedure Local_Handle_SPARK_File
        (Item : String; Index : Positive; Quit : in out Boolean);
      --  Wrapper for Handle_SPARK_File

      -----------------------------
      -- Local_Handle_SPARK_File --
      -----------------------------

      procedure Local_Handle_SPARK_File
        (Item : String; Index : Positive; Quit : in out Boolean) is
      begin
         pragma Unreferenced (Index);
         pragma Unreferenced (Quit);
         Handle_SPARK_File (Item);
      exception
         when others =>
            Ada.Text_IO.Put_Line
              (Ada.Text_IO.Standard_Error,
               "spark_report: error when processing file "
               & Item
               & ", skipping");
            Ada.Text_IO.Put_Line
              (Ada.Text_IO.Standard_Error,
               "spark_report: try cleaning proofs to remove this error");
      end Local_Handle_SPARK_File;

      procedure Iterate_SPARK is new
        GNAT.Directory_Operations.Iteration.Wildcard_Iterator
          (Action => Local_Handle_SPARK_File);

      Save_Dir : constant String := Ada.Directories.Current_Directory;

      --  Start of processing for Handle_Source_Dir

   begin
      Ada.Directories.Set_Directory (Dir);
      Iterate_SPARK (Path => "*." & VC_Kinds.SPARK_Suffix);
      Ada.Directories.Set_Directory (Save_Dir);
   exception
      when others =>
         Ada.Directories.Set_Directory (Save_Dir);
         raise;
   end Handle_Source_Dir;

   -----------------------
   -- Handle_SPARK_File --
   -----------------------

   procedure Handle_SPARK_File (Fn : String) is

      Dict      : constant JSON_Value := Read_File_Into_JSON (Fn);
      Has_Flow  : constant Boolean := Has_Field (Dict, "flow");
      Has_Proof : constant Boolean := Has_Field (Dict, "proof");
   begin
      Parse_Entity_Table (Get (Dict, "entities"));
      if Has_Flow then
         Handle_Items (Get (Get (Dict, "flow")));
      end if;
      if Has_Proof then
         Handle_Items (Get (Get (Dict, "proof")));
      end if;
      Handle_Items (Get (Get (Dict, "warn_error")));
   end Handle_SPARK_File;

   ------------------------
   -- Handle_SPARK_Files --
   ------------------------

   procedure Handle_SPARK_Files is
   begin
      if Has_Field (Info, "obj_dirs") then
         declare
            Ar : constant JSON_Array := Get (Info, "obj_dirs");
         begin
            for Var_Index in Positive range 1 .. Length (Ar) loop
               Handle_Source_Dir (Get (Get (Ar, Var_Index)));
            end loop;
         end;
      end if;
   end Handle_SPARK_Files;

   --------------
   -- Location --
   --------------

   function Location (V : JSON_Value) return SARIF.Types.location is
      File              : constant String := Get (Get (V, "file"));
      Line              : constant Integer := Get (Get (V, "line"));
      Col               : constant Integer := Get (Get (V, "col"));
      Logical_Locations : logicalLocation_Vector;
   begin
      --  ??? the vc_sloc (check_file, check_line etc) might be more
      --  appropriate, if present.
      if Has_Field (V, "entity") then
         Logical_Locations.Append
           (logicalLocation'
              (name   =>
                 To_Virtual_String (Subp_Name (From_JSON (Get (V, "entity")))),
               others => <>));
      end if;
      return
        SARIF.Types.location'
          (physicalLocation =>
             (True,
              physicalLocation'
                (artifactLocation =>
                   (True, (uri => To_Virtual_String (File), others => <>)),
                 region           =>
                   (True,
                    (startLine   => (True, Line),
                     startColumn => (True, Col),
                     others      => <>)),
                 others           => <>)),
           logicalLocations => Logical_Locations,
           others           => <>);
   end Location;

   ---------------
   -- Locations --
   ---------------

   function Locations (V : JSON_Value) return SARIF.Types.location_Vector is
      Result : SARIF.Types.location_Vector;
   begin
      Result.Append (Location (V));
      return Result;
   end Locations;

   -------------
   -- Message --
   -------------

   function Message (V : JSON_Value) return SARIF.Types.message is
      Result : SARIF.Types.message;
      Text   : constant String := Get (Get (V, "text"));
   begin
      Result.text := To_Virtual_String (Text);
      if Has_Field (V, "arguments") then
         declare
            Ar : constant JSON_Array := Get (V, "arguments");
         begin
            for Var_Index in Positive range 1 .. Length (Ar) loop
               declare
                  Arg : constant String := (Get (Get (Ar, Var_Index)));
               begin
                  Result.arguments.Append (To_Virtual_String (Arg));
               end;
            end loop;
         end;
      end if;
      return Result;
   end Message;

   -----------------------------
   -- Mk_Multi_Message_String --
   -----------------------------

   function Mk_Multi_Message_String
     (S : String) return Optional_multiformatMessageString is
   begin
      return (True, (text => To_Virtual_String (S), others => <>));
   end Mk_Multi_Message_String;

   -----------
   -- Rules --
   -----------

   function Rules return SARIF.Types.reportingDescriptor_Vector is
      result : SARIF.Types.reportingDescriptor_Vector;
   begin
      --  ??? filter based e.g. on actually present messages
      for K in Flow_Error_Kind loop
         result.Append
           (reportingDescriptor'
              (id               => To_Virtual_String (Rule_Name (K)),
               shortDescription => Mk_Multi_Message_String (Kind_Name (K)),
               fullDescription  => Mk_Multi_Message_String (Description (K)),
               others           => <>));
      end loop;

      for K in Flow_Check_Kind loop
         result.Append
           (reportingDescriptor'
              (id               => To_Virtual_String (Rule_Name (K)),
               shortDescription => Mk_Multi_Message_String (Kind_Name (K)),
               fullDescription  => Mk_Multi_Message_String (Description (K)),
               others           => <>));
      end loop;

      for K in Flow_Warning_Kind loop
         result.Append
           (reportingDescriptor'
              (id               => To_Virtual_String (Rule_Name (K)),
               shortDescription => Mk_Multi_Message_String (Kind_Name (K)),
               fullDescription  => Mk_Multi_Message_String (Description (K)),
               others           => <>));
      end loop;

      for K in VC_Kind loop
         result.Append
           (reportingDescriptor'
              (id               => To_Virtual_String (Rule_Name (K)),
               shortDescription => Mk_Multi_Message_String (Kind_Name (K)),
               fullDescription  => Mk_Multi_Message_String (Description (K)),
               others           => <>));
      end loop;

      for K in Misc_Warning_Kind loop
         result.Append
           (reportingDescriptor'
              (id              => To_Virtual_String (Kind_Name (K)),
               fullDescription => Mk_Multi_Message_String (Description (K)),
               others          => <>));
      end loop;

      return result;
   end Rules;

   --------------------
   -- SARIF_Location --
   --------------------

   function SARIF_Location (V : JSON_Value) return SARIF.Types.location is
      pragma Assert (Has_Field (V, "physicalLocation"));
      Ph   : constant JSON_Value := Get (V, "physicalLocation");
      pragma Assert (Has_Field (Ph, "uri"));
      pragma Assert (Has_Field (Ph, "region"));
      Reg  : constant JSON_Value := Get (Ph, "region");
      File : constant String := Get (Get (Ph, "uri"));
      Line : constant Integer := Get (Get (Reg, "startLine"));
      Col  : constant Integer := Get (Get (Reg, "startColumn"));
   begin
      return
        SARIF.Types.location'
          (id               =>
             (if Has_Field (V, "id")
              then (True, Integer'(Get (Get (V, "id"))))
              else (Is_Set => False)),
           physicalLocation =>
             (True,
              physicalLocation'
                (artifactLocation =>
                   (True, (uri => To_Virtual_String (File), others => <>)),
                 region           =>
                   (True,
                    (startLine   => (True, Line),
                     startColumn => (True, Col),
                     others      => <>)),
                 others           => <>)),
           others           => <>);
   end SARIF_Location;

   -----------------------------
   -- Severity_To_Result_Kind --
   -----------------------------

   function Severity_To_Result_Kind
     (S : String) return SARIF.Types.Enum.result_kind is
   begin
      if S = "info" then
         return SARIF.Types.Enum.pass;
      elsif S = "error" or else S = "high" then
         return SARIF.Types.Enum.fail;
      else
         return SARIF.Types.Enum.open;
      end if;
   end Severity_To_Result_Kind;

   ------------------------------
   -- Severity_To_Result_Level --
   ------------------------------

   function Severity_To_Result_Level
     (S : String) return SARIF.Types.Enum.result_level is
   begin
      if S = "error" then
         return SARIF.Types.Enum.error;
      elsif S = "warning" then
         return SARIF.Types.Enum.warning;
      else
         return SARIF.Types.Enum.none;
      end if;
   end Severity_To_Result_Level;

   ---------------------
   -- Tool_Invocation --
   ---------------------

   function Tool_Invocation return SARIF.Types.invocation is
   begin
      --  ??? add information about switches in project file, see Show_Header
      --  ??? add information about host, see Show_Header
      --  ??? property bags seem incorrectly supported by sarif-ada for now
      --  We set executionSuccessful to True as we only generate the SARIF
      --  report in this case.
      return
        invocation'
          (commandLine         =>
             To_Virtual_String (Build_Switches_String (Get (Info, "cmdline"))),
           endTimeUtc          => To_Virtual_String (End_Time),
           exitCode            => (True, Error_Code),
           executionSuccessful => True,
           others              => <>);
   end Tool_Invocation;

   --  Beginning of processing for Generate_SARIF_Report

begin
   My_Run.tool :=
     tool'
       (driver =>
          toolComponent'
            (name         => "GNATProve",
             version      => To_Virtual_String (SPARK2014_Version_String),
             organization => "AdaCore",
             rules        => Rules,
             others       => <>),
        others => <>);
   My_Run.invocations.Append (Tool_Invocation);
   My_Results.Clear (Is_Null => False);
   Handle_SPARK_Files;
   My_Run.results := My_Results;
   Root.runs.Append (My_Run);
   Writer.Set_Stream (Output'Unchecked_Access);
   Output.Create (To_Virtual_String (Filename), "utf-8");
   Writer.Start_Document;
   Outputs.Output_Root (Writer, Root);
   Writer.End_Document;
end Generate_SARIF_Report;
