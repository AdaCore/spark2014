------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                    S P A R K _ R E P O R T _ D A T A                     --
--                                                                          --
--                                 S p e c                                  --
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

with Ada.Containers.Ordered_Maps;
with Ada.Containers.Vectors;
with Ada.Containers.Doubly_Linked_Lists;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Assumption_Types;      use Assumption_Types;
with Assumptions;
with String_Utils;          use String_Utils;
with VC_Kinds;              use VC_Kinds;

--  Data shared by the text and SARIF report consumers. Entity references
--  are unit-local indices, resolved against the unit's own entity table.
--  No JSON values or raw subtrees are retained.

package SPARK_Report_Data is
   type Entity_Reference is new Natural;
   No_Entity_Reference : constant Entity_Reference := 0;

   subtype Valid_Entity_Reference is
     Entity_Reference range 1 .. Entity_Reference'Last;
   --  Nonzero reference into the current unit's entity table

   type Optional_Text is record
      Present : Boolean := False;
      Value   : Unbounded_String;
   end record;

   type Source_Location is record
      File   : Unbounded_String;
      Line   : Natural := 0;
      Column : Natural := 0;
      Entity : Entity_Reference := No_Entity_Reference;
   end record;

   type Related_Location is record
      Sloc   : Source_Location;
      Has_Id : Boolean := False;
      Id     : Integer := 0;
   end record;
   package Related_Location_Vectors is new
     Ada.Containers.Vectors (Positive, Related_Location);

   type Suppression_Kind is
     (No_Suppression, Warning_Suppression, Check_Suppression);

   type Suppression_Info (Kind : Suppression_Kind := No_Suppression) is record
      case Kind is
         when No_Suppression | Warning_Suppression =>
            null;

         when Check_Suppression =>
            Reason        : Unbounded_String;
            Annotation    : Unbounded_String;
            Justification : Unbounded_String;
      end case;
   end record;

   type Diagnostic is record
      Sloc             : Source_Location;
      Severity         : Unbounded_String;
      Rule             : Unbounded_String;
      Text             : Unbounded_String;
      Arguments        : String_Lists.List;
      Suppression      : Suppression_Info;
      Reason_For_Check : Optional_Text;
      Explain_Code     : Optional_Text;
      Related          : Related_Location_Vectors.Vector;
      How_Proved       : Prover_Category := PC_Flow;
      Has_How_Proved   : Boolean := False;
      Stats            : Prover_Stat_Maps.Map;
      Has_Stats        : Boolean := False;
   end record;
   package Diagnostic_Vectors is new
     Ada.Containers.Vectors (Positive, Diagnostic);
   package Location_Vectors is new
     Ada.Containers.Vectors (Positive, Source_Location);
   package Entity_Maps is new
     Ada.Containers.Ordered_Maps (Valid_Entity_Reference, Subp_Type);
   package Entity_Vectors is new
     Ada.Containers.Vectors (Positive, Valid_Entity_Reference);
   type SPARK_Status is record
      Entity : Valid_Entity_Reference;
      Status : SPARK_Mode_Status;
   end record;
   package Status_Vectors is new
     Ada.Containers.Vectors (Positive, SPARK_Status);

   type Global_Mode is (Input_Mode, In_Out_Mode, Output_Mode, Proof_In_Mode);
   type Global_Names is record
      Present : Boolean := False;
      Names   : String_Lists.List;
   end record;
   type Global_Modes is array (Global_Mode) of Global_Names;
   type Generated_Global is record
      Entity         : Valid_Entity_Reference;
      Global         : Global_Modes;
      Refined_Global : Global_Modes;
   end record;
   package Global_Vectors is new
     Ada.Containers.Vectors (Positive, Generated_Global);

   type Token_Reference is record
      Predicate : Assumptions.Claim_Kind := Assumptions.Claim_AoRTE;
      Entity    : Valid_Entity_Reference := 1;
   end record;
   package Token_Vectors is new
     Ada.Containers.Vectors (Positive, Token_Reference);
   type Rule_Reference is record
      Claim       : Token_Reference;
      Assumptions : Token_Vectors.Vector;
   end record;
   package Rule_Lists is new
     Ada.Containers.Doubly_Linked_Lists (Rule_Reference);

   type Unit_Data is record
      Entities          : Entity_Maps.Map;
      Statuses          : Status_Vectors.Vector;
      Skip_Flow_Proof   : Entity_Vectors.Vector;
      Skip_Proof        : Entity_Vectors.Vector;
      Progress          : Analysis_Progress := Progress_None;
      Stop_Reason       : Stop_Reason_Type := Stop_Reason_None;
      Has_Progress      : Boolean := False;
      Has_Stop_Reason   : Boolean := False;
      Has_Entities      : Boolean := False;
      Flow              : Diagnostic_Vectors.Vector;
      Proof             : Diagnostic_Vectors.Vector;
      Warn_Error        : Diagnostic_Vectors.Vector;
      Manifest_Warnings : Diagnostic_Vectors.Vector;
      Pragma_Assume     : Location_Vectors.Vector;
      Assumptions       : Rule_Lists.List;
      Globals           : Global_Vectors.Vector;
   end record;

   function Read
     (Input : String; Read_Assumptions : Boolean := True) return Unit_Data;
   function Read_File
     (Filename : String; Read_Assumptions : Boolean := True) return Unit_Data;
   --  Decode report fields into owned application records. Unknown members
   --  and opaque proof payloads are ignored after JSON parsing.

   function Subprogram
     (Data : Unit_Data; Entity : Valid_Entity_Reference) return Subp_Type;

   function Resolve_Assumptions
     (Data : Unit_Data) return Assumptions.Rule_Lists.List;
end SPARK_Report_Data;
