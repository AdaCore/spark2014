------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                    S P A R K _ R E P O R T _ D A T A                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2026, AdaCore                        --
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

with Call;          use Call;
with GNATCOLL.JSON; use GNATCOLL.JSON;
with SPARK_JSON_Entities;

package body SPARK_Report_Data is

   function Read_Optional
     (Value : JSON_Value; Name : String) return Optional_Text;
   function Read_Strings (Value : JSON_Value) return String_Lists.List;
   function Read_Location (Value : JSON_Value) return Source_Location;
   function Read_Diagnostics
     (Value : JSON_Value) return Diagnostic_Vectors.Vector;
   function Read_Modes (Value : JSON_Value) return Global_Modes;
   function Read_Token (Value : JSON_Value) return Token_Reference;

   ----------------
   -- Subprogram --
   ----------------

   function Subprogram
     (Data : Unit_Data; Entity : Valid_Entity_Reference) return Subp_Type is
   begin
      return Data.Entities.Element (Entity);
   end Subprogram;

   -------------------------
   -- Resolve_Assumptions --
   -------------------------

   function Resolve_Assumptions
     (Data : Unit_Data) return Assumptions.Rule_Lists.List
   is
      Result : Assumptions.Rule_Lists.List;
   begin
      for Ref of Data.Assumptions loop
         declare
            Item : Assumptions.Rule :=
              (Claim       =>
                 (Ref.Claim.Predicate, Subprogram (Data, Ref.Claim.Entity)),
               Assumptions => <>);
         begin
            for T of Ref.Assumptions loop
               Item.Assumptions.Include
                 ((T.Predicate, Subprogram (Data, T.Entity)));
            end loop;
            Result.Append (Item);
         end;
      end loop;
      return Result;
   end Resolve_Assumptions;

   -------------------
   -- Read_Optional --
   -------------------

   function Read_Optional
     (Value : JSON_Value; Name : String) return Optional_Text is
   begin
      if Has_Field (Value, Name) then
         return (True, To_Unbounded_String (String'(Get (Value, Name))));
      else
         return (others => <>);
      end if;
   end Read_Optional;

   ------------------
   -- Read_Strings --
   ------------------

   function Read_Strings (Value : JSON_Value) return String_Lists.List is
      Result : String_Lists.List;
   begin
      for Item of JSON_Array'(Get (Value)) loop
         Result.Append (String'(Get (Item)));
      end loop;
      return Result;
   end Read_Strings;

   -------------------
   -- Read_Location --
   -------------------

   function Read_Location (Value : JSON_Value) return Source_Location is
      Result : Source_Location :=
        (File   => To_Unbounded_String (String'(Get (Value, "file"))),
         Line   => Get (Get (Value, "line")),
         Column => Get (Get (Value, "col")),
         Entity => No_Entity_Reference);
   begin
      if Has_Field (Value, "entity") then
         Result.Entity :=
           Valid_Entity_Reference (Integer'(Get (Get (Value, "entity"))));
      end if;
      return Result;
   end Read_Location;

   ----------------------
   -- Read_Diagnostics --
   ----------------------

   function Read_Diagnostics
     (Value : JSON_Value) return Diagnostic_Vectors.Vector
   is
      Result : Diagnostic_Vectors.Vector;
   begin
      for Source of JSON_Array'(Get (Value)) loop
         declare
            Message : constant JSON_Value := Get (Source, "message");
            Item    : Diagnostic;
         begin
            Item.Sloc := Read_Location (Source);
            Item.Severity :=
              To_Unbounded_String (String'(Get (Source, "severity")));
            Item.Rule := To_Unbounded_String (String'(Get (Source, "rule")));
            Item.Text := To_Unbounded_String (String'(Get (Message, "text")));
            if Has_Field (Message, "arguments") then
               Item.Arguments := Read_Strings (Get (Message, "arguments"));
            end if;
            if Has_Field (Source, "suppressed") then
               if Item.Severity = "warning" then
                  Item.Suppression := (Kind => Warning_Suppression);
               else
                  Item.Suppression :=
                    (Kind          => Check_Suppression,
                     Reason        =>
                       Read_Optional (Source, "suppressed").Value,
                     Annotation    =>
                       Read_Optional (Source, "annot_kind").Value,
                     Justification =>
                       Read_Optional (Source, "justif_msg").Value);
               end if;
            end if;
            Item.Reason_For_Check := Read_Optional (Source, "reasonForCheck");
            Item.Explain_Code := Read_Optional (Source, "explainCode");
            if Has_Field (Source, "how_proved") then
               Item.How_Proved := From_JSON (Get (Source, "how_proved"));
               Item.Has_How_Proved := True;
            end if;
            if Has_Field (Source, "stats") then
               Item.Stats := From_JSON (Get (Source, "stats"));
               Item.Has_Stats := True;
            end if;
            if Has_Field (Source, "relatedLocations") then
               for Related of
                 JSON_Array'(Get (Get (Source, "relatedLocations")))
               loop
                  declare
                     Physical : constant JSON_Value :=
                       Get (Related, "physicalLocation");
                     Region   : constant JSON_Value :=
                       Get (Physical, "region");
                     Location : Related_Location :=
                       (Sloc   =>
                          (File   =>
                             To_Unbounded_String
                               (String'(Get (Physical, "uri"))),
                           Line   => Get (Get (Region, "startLine")),
                           Column => Get (Get (Region, "startColumn")),
                           Entity => No_Entity_Reference),
                        others => <>);
                  begin
                     if Has_Field (Related, "id") then
                        Location.Id := Get (Get (Related, "id"));
                        Location.Has_Id := True;
                     end if;
                     Item.Related.Append (Location);
                  end;
               end loop;
            end if;
            Result.Append (Item);
         end;
      end loop;
      return Result;
   end Read_Diagnostics;

   ----------------
   -- Read_Modes --
   ----------------

   function Read_Modes (Value : JSON_Value) return Global_Modes is
      Result : Global_Modes;
   begin
      for Mode in Global_Mode loop
         declare
            Name : constant String :=
              (case Mode is
                 when Input_Mode    => "Input",
                 when In_Out_Mode   => "In_Out",
                 when Output_Mode   => "Output",
                 when Proof_In_Mode => "Proof_In");
         begin
            if Has_Field (Value, Name) then
               Result (Mode) := (True, Read_Strings (Get (Value, Name)));
            end if;
         end;
      end loop;
      return Result;
   end Read_Modes;

   ----------------
   -- Read_Token --
   ----------------

   function Read_Token (Value : JSON_Value) return Token_Reference is
   begin
      return
        (Predicate =>
           Assumptions.Claim_Kind'Value (String'(Get (Value, "predicate"))),
         Entity    =>
           Valid_Entity_Reference (Integer'(Get (Get (Value, "arg")))));
   end Read_Token;

   ------------
   -- Decode --
   ------------

   function Decode
     (Value : JSON_Value; Read_Assumptions : Boolean := True) return Unit_Data
   is
      Result : Unit_Data;

      procedure Read_Status (Name : UTF8_String; Value : JSON_Value);
      procedure Read_Global (Name : UTF8_String; Value : JSON_Value);

      -----------------
      -- Read_Status --
      -----------------

      procedure Read_Status (Name : UTF8_String; Value : JSON_Value) is
      begin
         Result.Statuses.Append
           (SPARK_Status'
              (Valid_Entity_Reference'Value (Name), From_JSON (Value)));
      end Read_Status;

      -----------------
      -- Read_Global --
      -----------------

      procedure Read_Global (Name : UTF8_String; Value : JSON_Value) is
      begin
         Result.Globals.Append
           (Generated_Global'
              (Entity         => Valid_Entity_Reference'Value (Name),
               Global         => Read_Modes (Get (Value, "Global")),
               Refined_Global => Read_Modes (Get (Value, "Refined_Global"))));
      end Read_Global;

   begin
      if Kind (Value) /= JSON_Object_Type then
         raise Invalid_JSON_Stream with "expected .spark object";
      end if;
      if Has_Field (Value, "entities") then
         for Entity of
           SPARK_JSON_Entities.Parse_Entity_Table (Get (Value, "entities"))
         loop
            declare
               Slocs : My_Sloc;
            begin
               for Sloc of Entity.Sloc loop
                  Slocs.Append
                    (Mk_Base_Sloc
                       (To_String (Sloc.File), Sloc.Line, Sloc.Column));
               end loop;
               Result.Entities.Insert
                 (Valid_Entity_Reference (Entity.Key_Index),
                  Mk_Subp
                    (To_String (Entity.Name),
                     Slocs,
                     To_String (Entity.Manifest_Kind),
                     To_String (Entity.Manifest_Profile)));
            end;
         end loop;
         Result.Has_Entities := True;
      end if;
      if Has_Field (Value, "progress") then
         Result.Progress :=
           Analysis_Progress'Value (String'(Get (Value, "progress")));
         Result.Has_Progress := True;
      end if;
      if Has_Field (Value, "stop_reason") then
         Result.Stop_Reason :=
           Stop_Reason_Type'Value (String'(Get (Value, "stop_reason")));
         Result.Has_Stop_Reason := True;
      end if;
      if Has_Field (Value, "spark") then
         Map_JSON_Object (Get (Value, "spark"), Read_Status'Access);
      end if;
      if Has_Field (Value, "skip_flow_proof") then
         for Entity of JSON_Array'(Get (Get (Value, "skip_flow_proof"))) loop
            Result.Skip_Flow_Proof.Append
              (Valid_Entity_Reference (Integer'(Get (Entity))));
         end loop;
      end if;
      if Has_Field (Value, "skip_proof") then
         for Entity of JSON_Array'(Get (Get (Value, "skip_proof"))) loop
            Result.Skip_Proof.Append
              (Valid_Entity_Reference (Integer'(Get (Entity))));
         end loop;
      end if;
      if Has_Field (Value, "flow") then
         Result.Flow := Read_Diagnostics (Get (Value, "flow"));
      end if;
      if Has_Field (Value, "proof") then
         Result.Proof := Read_Diagnostics (Get (Value, "proof"));
      end if;
      if Has_Field (Value, "warn_error") then
         Result.Warn_Error := Read_Diagnostics (Get (Value, "warn_error"));
      end if;
      if Has_Field (Value, "manifest_warnings") then
         Result.Manifest_Warnings :=
           Read_Diagnostics (Get (Value, "manifest_warnings"));
      end if;
      if Has_Field (Value, "pragma_assume") then
         for Location of JSON_Array'(Get (Get (Value, "pragma_assume"))) loop
            Result.Pragma_Assume.Append (Read_Location (Location));
         end loop;
      end if;
      if Read_Assumptions and then Has_Field (Value, "assumptions") then
         for Source of JSON_Array'(Get (Get (Value, "assumptions"))) loop
            declare
               Item : Rule_Reference :=
                 (Claim => Read_Token (Get (Source, "claim")), others => <>);
            begin
               for Token of JSON_Array'(Get (Get (Source, "assumptions"))) loop
                  Item.Assumptions.Append (Read_Token (Token));
               end loop;
               Result.Assumptions.Append (Item);
            end;
         end loop;
      end if;
      if Has_Field (Value, "generated_globals") then
         Map_JSON_Object
           (Get (Value, "generated_globals"), Read_Global'Access);
      end if;
      return Result;
   end Decode;

   ----------
   -- Read --
   ----------

   function Read
     (Input : String; Read_Assumptions : Boolean := True) return Unit_Data is
   begin
      return Decode (GNATCOLL.JSON.Read (Input), Read_Assumptions);
   end Read;

   ---------------
   -- Read_File --
   ---------------

   function Read_File
     (Filename : String; Read_Assumptions : Boolean := True) return Unit_Data
   is
   begin
      return Decode (Read_File_Into_JSON (Filename), Read_Assumptions);
   end Read_File;
end SPARK_Report_Data;
