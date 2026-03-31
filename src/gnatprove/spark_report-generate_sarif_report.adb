------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--   S P A R K _ R E P O R T - G E N E R A T E _ S A R I F _ R E P O R T    --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2026, AdaCore                     --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers.Indefinite_Hashed_Maps;
with Ada.Strings.Fixed;
with Ada.Strings.Hash;
with Ada.Strings.Unbounded;
with Configuration;
with GNAT.OS_Lib;
with GPR2.Project.Tree;
with SARIF.Types;             use SARIF.Types;
with SARIF.Types.Outputs;
with VSS.JSON.Push_Writers;
with VSS.JSON.Streams;
with VSS.Strings;
with VSS.Strings.Conversions; use VSS.Strings.Conversions;
with VSS.Text_Streams.File_Output;

separate (Spark_Report)
procedure Generate_SARIF_Report
  (Filename           : String;
   SPARK_Files        : SPARK_File_Lists.List;
   Command_Line_Image : String;
   Error_Code         : Integer;
   Tree               : GPR2.Project.Tree.Object)
is
   Root       : SARIF.Types.Root;
   My_Run     : run;
   My_Results : SARIF.Types.result_Vector;

   Output : aliased VSS.Text_Streams.File_Output.File_Output_Text_Stream;
   Writer : VSS.JSON.Push_Writers.JSON_Simple_Push_Writer;

   package Base_URI_Maps is new
     Ada.Containers.Indefinite_Hashed_Maps
       (Key_Type        => String,
        Element_Type    => String,
        Hash            => Ada.Strings.Hash,
        Equivalent_Keys => "=",
        "="             => "=");
   --  Maps SARIF uriBaseId identifiers to canonical directory paths.
   --  Paths always end with a directory separator.

   Base_URIs : Base_URI_Maps.Map;
   --  Maps SARIF uriBaseId identifiers to canonical directory paths.
   --  Populated at the start of processing from CL_Switches.SARIF_Base_URIs.

   function Tool_Invocation return SARIF.Types.invocation;
   function Rules return SARIF.Types.reportingDescriptor_Vector;
   --  Helper functions that generate subsections of the SARIF report

   function Mk_Multi_Message_String
     (S : String) return Optional_multiformatMessageString;
   --  Helper to create a multiformatMessageString object from a simple String

   function Resolve_Source (Simple : String) return String;
   --  Resolve a source basename to its full absolute path via the project
   --  tree.
   --  Returns an empty string when the source is not found.

   function Normalize_URI_Path (Path : String) return String;
   --  Replace every backslash in Path with a forward slash and return the
   --  result. Used to make URI path components portable across platforms.

   function Path_To_File_URI (Path : String) return String;
   --  Convert an absolute path to a file:// URI with forward slashes.

   function Make_Artifact_Location
     (Simple_File : String) return SARIF.Types.artifactLocation;
   --  Build a SARIF artifactLocation for the given source basename, resolving
   --  it to a full path and applying the base URI map.

   function Build_Original_Uri_Base_Ids return SARIF.Types.Any_Object;
   --  Build the run.originalUriBaseIds value from Base_URIs.

   procedure Handle_SPARK_Files;
   --  Parse all .spark files

   procedure Handle_SPARK_File (Dict : JSON_Value);
   --  Extract all information from a single already-parsed SPARK file

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

   function Ensure_Trailing_Sep (S : String) return String;
   --  Ensure that S ends with a directory separator, adding one if needed.

   ---------------------------------
   -- Build_Original_Uri_Base_Ids --
   ---------------------------------

   function Build_Original_Uri_Base_Ids return SARIF.Types.Any_Object is
      use VSS.JSON.Streams;
      Result : SARIF.Types.Any_Object;
   begin
      Result.Append ((Kind => Start_Object));
      for C in Base_URIs.Iterate loop
         declare
            Id  : constant String := Base_URI_Maps.Key (C);
            URI : constant String :=
              Path_To_File_URI (Base_URI_Maps.Element (C));
            --  Element already ends with a directory separator, so the URI
            --  ends with '/' as the SARIF spec requires.
         begin
            Result.Append
              ((Kind => Key_Name, Key_Name => To_Virtual_String (Id)));
            Result.Append ((Kind => Start_Object));
            Result.Append
              ((Kind => Key_Name, Key_Name => To_Virtual_String ("uri")));
            Result.Append
              ((Kind         => String_Value,
                String_Value => To_Virtual_String (URI)));
            Result.Append ((Kind => End_Object));
         end;
      end loop;
      Result.Append ((Kind => End_Object));
      return Result;
   end Build_Original_Uri_Base_Ids;

   -------------------------
   -- Ensure_Trailing_Sep --
   -------------------------

   function Ensure_Trailing_Sep (S : String) return String is
      Sep : constant Character := GNAT.OS_Lib.Directory_Separator;
   begin
      if S'Length > 0 and then S (S'Last) = Sep then
         return S;
      else
         return S & Sep;
      end if;
   end Ensure_Trailing_Sep;

   ------------------------
   -- Normalize_URI_Path --
   ------------------------

   function Normalize_URI_Path (Path : String) return String is
      S : String := Path;
   begin
      for C of S loop
         if C = '\' then
            C := '/';
         end if;
      end loop;
      return S;
   end Normalize_URI_Path;

   ----------------------
   -- Path_To_File_URI --
   ----------------------

   function Path_To_File_URI (Path : String) return String is
      S : constant String := Normalize_URI_Path (Path);
   begin
      if S'Length > 0 and then S (S'First) = '/' then
         return "file://" & S;
      else
         return "file:///" & S;
      end if;
   end Path_To_File_URI;

   ----------------------------
   -- Make_Artifact_Location --
   ----------------------------

   function Make_Artifact_Location
     (Simple_File : String) return SARIF.Types.artifactLocation
   is
      Full        : constant String := Resolve_Source (Simple_File);
      Best_Id     : Unbounded_String;
      Best_Prefix : Unbounded_String;
   begin
      if Full /= "" then
         for C in Base_URIs.Iterate loop
            declare
               Prefix : constant String := Base_URI_Maps.Element (C);
            begin
               if Full'Length >= Prefix'Length
                 and then
                   Full (Full'First .. Full'First + Prefix'Length - 1) = Prefix
                 and then Prefix'Length > Length (Best_Prefix)
               then
                  Best_Id := To_Unbounded_String (Base_URI_Maps.Key (C));
                  Best_Prefix := To_Unbounded_String (Prefix);
               end if;
            end;
         end loop;
      end if;

      if Length (Best_Id) > 0 then
         return
           (uri       =>
              To_Virtual_String
                (Normalize_URI_Path
                   (Full (Full'First + Length (Best_Prefix) .. Full'Last))),
            uriBaseId => To_Virtual_String (To_String (Best_Id)),
            others    => <>);
      elsif Full /= "" then
         return
           (uri => To_Virtual_String (Path_To_File_URI (Full)), others => <>);
      else
         --  Source not found in project: emit simple name as relative URI
         return (uri => To_Virtual_String (Simple_File), others => <>);
      end if;
   end Make_Artifact_Location;

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
   -- Handle_SPARK_File --
   -----------------------

   procedure Handle_SPARK_File (Dict : JSON_Value) is

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
      for File_Data of SPARK_Files loop
         begin
            Handle_SPARK_File (File_Data.Data);
         exception
            when others =>
               Ada.Text_IO.Put_Line
                 (Ada.Text_IO.Standard_Error,
                  "spark_report: error when processing file "
                  & To_String (File_Data.File)
                  & ", skipping");
               Ada.Text_IO.Put_Line
                 (Ada.Text_IO.Standard_Error,
                  "spark_report: try cleaning proofs to remove this error");
         end;
      end loop;
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
                (artifactLocation => (True, Make_Artifact_Location (File)),
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

   --------------------
   -- Resolve_Source --
   --------------------

   function Resolve_Source (Simple : String) return String
   is (Configuration.Source_Full_Path (Tree, Simple));

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
              (id               => To_Virtual_String (Kind_Name (K)),
               shortDescription => Mk_Multi_Message_String (Description (K)),
               fullDescription  => Mk_Multi_Message_String (Description (K)),
               others           => <>));
      end loop;

      --  Add GNATprove annotation rules
      for K in GNATprove_Annotation_Kind loop
         result.Append
           (reportingDescriptor'
              (id               => To_Virtual_String (Annotation_Tag (K)),
               shortDescription =>
                 Mk_Multi_Message_String (Pretty_Annotation_Name (K)),
               fullDescription  =>
                 Mk_Multi_Message_String (Annotation_Description (K)),
               others           => <>));
      end loop;

      --  Add unsupported construct rules
      for K in Unsupported_Kind loop
         declare
            Rule_ID : constant String := Unsupported_Tag (K);
         begin
            result.Append
              (reportingDescriptor'
                 (id               => To_Virtual_String (Rule_ID),
                  shortDescription =>
                    Mk_Multi_Message_String (Unsupported_Kind_Name (K)),
                  fullDescription  =>
                    Mk_Multi_Message_String (Description (K)),
                  others           => <>));
         end;
      end loop;

      --  Add violation rules
      for K in Violation_Kind loop
         declare
            Rule_ID : constant String := Violation_Tag (K);
         begin
            result.Append
              (reportingDescriptor'
                 (id               => To_Virtual_String (Rule_ID),
                  shortDescription =>
                    Mk_Multi_Message_String (Violation_Kind_Name (K)),
                  fullDescription  =>
                    Mk_Multi_Message_String (Violation_Description (K)),
                  others           => <>));
         end;
      end loop;

      --  Add rule for GNAT front-end diagnostics
      result.Append
        (reportingDescriptor'
           (id               => To_Virtual_String ("GNAT"),
            shortDescription => Mk_Multi_Message_String ("GNAT Diagnostic"),
            fullDescription  =>
              Mk_Multi_Message_String
                ("Diagnostic message emitted by the GNAT front-end"),
            others           => <>));

      --  Add catch-all rule for errors without classification
      result.Append
        (reportingDescriptor'
           (id               => To_Virtual_String (Misc_Error_Tag),
            shortDescription => Mk_Multi_Message_String (Misc_Error_Name),
            fullDescription  =>
              Mk_Multi_Message_String (Misc_Error_Description),
            others           => <>));

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
                (artifactLocation => (True, Make_Artifact_Location (File)),
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
          (commandLine         => To_Virtual_String (Command_Line_Image),
           endTimeUtc          => To_Virtual_String (End_Time),
           exitCode            => (True, Error_Code),
           executionSuccessful => True,
           others              => <>);
   end Tool_Invocation;

begin
   for Raw of Configuration.CL_Switches.SARIF_Base_URIs loop
      declare
         Colon : constant Natural := Ada.Strings.Fixed.Index (Raw, ":");
         Id    : constant String := Raw (Raw'First .. Colon - 1);
         Path  : constant String := Raw (Colon + 1 .. Raw'Last);
      begin
         Base_URIs.Include (Id, Ensure_Trailing_Sep (Path));
      end;
   end loop;

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
   My_Run.originalUriBaseIds := Build_Original_Uri_Base_Ids;
   My_Results.Clear (Is_Null => False);
   Handle_SPARK_Files;
   My_Run.results := My_Results;
   Root.runs.Append (My_Run);
   Root.schema :=
     To_Virtual_String
       ("https://docs.oasis-open.org/sarif/sarif/v2.1.0/errata01/os/"
        & "schemas/sarif-schema-2.1.0.json");
   Writer.Set_Stream (Output'Unchecked_Access);
   Output.Create (To_Virtual_String (Filename), "utf-8");
   Writer.Start_Document;
   Outputs.Output_Root (Writer, Root);
   Writer.End_Document;
end Generate_SARIF_Report;
