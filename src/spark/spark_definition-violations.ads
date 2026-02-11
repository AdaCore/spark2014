------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              S P A R K _ D E F I N I T I O N - V I O L A T I O N         --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                     Copyright (C) 2020-2026, AdaCore                     --
--              Copyright (C) 2014-2026, Capgemini Engineering              --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers.Indefinite_Hashed_Maps;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Atree;                 use Atree;
with Errout_Wrapper;        use Errout_Wrapper;
with Gnat2Why_Args;         use Gnat2Why_Args;
with Opt;                   use Opt;
with VC_Kinds;              use VC_Kinds;

private package SPARK_Definition.Violations is

   package Violation_Root_Causes is new
     Ada.Containers.Indefinite_Hashed_Maps
       (Key_Type        => Node_Id,
        Element_Type    => String,
        Hash            => Node_Hash,
        Equivalent_Keys => "=",
        "="             => "=");
   use Violation_Root_Causes;

   Current_SPARK_Pragma : Node_Id := Types.Empty;
   --  The current applicable SPARK_Mode pragma, if any, to reference in error
   --  messages when a violation is encountered.

   Current_Delayed_Aspect_Type : Entity_Id := Types.Empty;
   --  When processing delayed aspect type (e.g. Predicate) this is set to the
   --  delayed type itself; used to reference the type in the error message.

   Current_Incomplete_Type : Entity_Id := Types.Empty;
   --  When processing incomplete types, this is set to the access type to the
   --  incomplete type; used to reference the type in the error message.

   Emit_Messages : Boolean := True;
   --  Messages are emitted only if this flag is set

   Violation_Detected : Boolean := False;
   --  Set to True when a violation is detected

   Violation_Root_Cause : Violation_Root_Causes.Map;
   --  Mapping from nodes not in SPARK to a description of the root cause
   --  of the underlying violation. This is used in error messages when the
   --  violation originates in that node.

   Last_Violation_Root_Cause_Node : Node_Id := Types.Empty;
   --  Last node which had a corresponding root cause for which a violation
   --  was detected. This node is used for the analysis of entities, and is
   --  saved/restored around Mark_Entity. Its value is not relevant outside
   --  of the analysis of an entity.

   function Emit_Warning_Info_Messages return Boolean
   is (Emit_Messages
       and then Gnat2Why_Args.Limit_Subp = Null_Unbounded_String
       and then Gnat2Why_Args.Limit_Name = Null_Unbounded_String);
   --  Emit warning/info messages only when messages should be emitted, and
   --  analysis is not restricted to a single subprogram/line (typically during
   --  interactive use in IDEs), to avoid reporting messages on pieces of code
   --  not belonging to the analyzed subprogram/line.

   function Get_Violation_Root_Cause (N : Node_Id) return String
   is (if Violation_Root_Cause.Contains (N)
       then Violation_Root_Cause.Element (N)
       else "");
   --  Return a message explaining the root cause of the violation in N not
   --  being in SPARK, if any, or the empty string otherwise.

   procedure Add_Violation_Root_Cause (N : Node_Id; Msg : String)
     --  Add a message explaining the root cause of the violation in N not
     --  being in SPARK.
   with Pre => Emit_Messages and then Present (N) and then Msg /= "";

   procedure Add_Violation_Root_Cause (N : Node_Id; From : Node_Id)
     --  Propagate the root cause message explaining the violation in From
     --  not being in SPARK to N.
   with Pre => Emit_Messages;

   function SPARK_Pragma_Is (Mode : Opt.SPARK_Mode_Type) return Boolean
   with
     Global => (Input => (Current_SPARK_Pragma, Current_Delayed_Aspect_Type));
   --  Returns True iff Current_SPARK_Pragma is not Empty, and corresponds to
   --  the given Mode.

   procedure Mark_Unsupported
     (Kind     : Unsupported_Kind;
      N        : Node_Id;
      Names    : Node_Lists.List := Node_Lists.Empty;
      Name     : String := "";
      Cont_Msg : Message := No_Message)
   with
     Global => (Output => Violation_Detected, Input => Current_SPARK_Pragma);
   --  Mark node N as an unsupported SPARK construct. An error message is
   --  issued if current SPARK_Mode is On. Cont_Msg is a continuous message
   --  when specified.

   procedure Mark_Incorrect_Use_Of_Annotation
     (Kind        : Incorrect_Annotation_Kind;
      N           : Node_Id;
      Msg         : String := "";
      From_Aspect : Boolean := False;
      Name        : String := "";
      Snd_Name    : String := "";
      Names       : Node_Lists.List := Node_Lists.Empty;
      Cont_Msg    : Message := No_Message)
   with
     Global => (Output => Violation_Detected, Input => Current_SPARK_Pragma);
   --  Mark node N as an incorrect use of a GNATprove annotation. An error
   --  issued if current SPARK_Mode is On.
   --  If supplied, use Name to get the annotation name. Otherwise, use Kind if
   --  it is a Specific_Annotation_Kind.
   --  From_Aspect and Snd_Name are used to pretty print the annotation as a
   --  pragma/aspect for some messages.
   --  If Cont_Msg is set, a continuation message is issued.
   --  If Names is set, use this to replace & in error messages.

   procedure Mark_Violation
     (Kind     : Violation_Kind;
      N        : Node_Id;
      Msg      : String := "";
      Names    : Node_Lists.List := Node_Lists.Empty;
      Cont_Msg : String := "")
   with
     Global => (Output => Violation_Detected, Input => Current_SPARK_Pragma);
   --  Mark node N as a violation of SPARK. An error message pointing to the
   --  current SPARK_Mode pragma/aspect is issued if current SPARK_Mode is On.
   --  If Cont_Msg is set, a continuation message is issued.
   --  If Names is set, use this to replace & in error messages.

   procedure Mark_Violation
     (N : Node_Id; From : Entity_Id; Cont_Msg : String := "")
   with
     Global => (Output => Violation_Detected, Input => Current_SPARK_Pragma);
   --  Mark node N as a violation of SPARK, due to the use of entity
   --  From which is not in SPARK. An error message is issued if current
   --  SPARK_Mode is On.

   procedure Mark_Force_Violation
     (E : Entity_Id; Reason : Message := No_Message);
   --  Register a violation on an entity E if it is not in SPARK regardless of
   --  the SPARK_Mode.

   procedure Mark_Violation_In_Tasking (N : Node_Id)
   with
     Global => (Output => Violation_Detected, Input => Current_SPARK_Pragma),
     Pre    => not Is_SPARK_Tasking_Configuration;
   --  Mark node N as a violation of SPARK because of unsupported tasking
   --  configuration. An error message is issued if current SPARK_Mode is
   --  On.

   Ravenscar_Profile_Result : Boolean := False;
   --  This switch memoizes the result of Ravenscar_Profile function calls
   --  for improved efficiency. Valid only if Ravenscar_Profile_Cached is
   --  True. Note: if this switch is ever set True, it is never turned off
   --  again.

   Ravenscar_Profile_Cached : Boolean := False;
   --  This flag is set to True if the Ravenscar_Profile_Result contains the
   --  correct cached result of Ravenscar_Profile calls.

   function GNATprove_Tasking_Profile return Boolean;
   --  Tests if configuration pragmas and restrictions corresponding to the
   --  tasking profile supported by the GNATprove are currently in effect
   --  (set by pragma Profile or by an appropriate set of individual
   --  Restrictions pragmas). Returns True only if all the required settings
   --  are set.

   function Sequential_Elaboration return Boolean
   is
      --  Check if Partition_Elaboration_Policy is set to Sequential
      (Partition_Elaboration_Policy = 'S');

   function Is_SPARK_Tasking_Configuration return Boolean
   is
      --  Check tasking configuration required by SPARK and possibly mark
      --  violation on node N.
      (GNATprove_Tasking_Profile and then Sequential_Elaboration);

end SPARK_Definition.Violations;
