------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                 F L O W . G E N E R A T E D _ G L O B A L S              --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2015-2019, Altran UK Limited                --
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
------------------------------------------------------------------------------

--  This package implements writing, reading and computing global contracts

with Atree;                              use Atree;
with Common_Containers;                  use Common_Containers;
with Einfo;                              use Einfo;
with Flow;                               use Flow;
with Flow_Types;                         use Flow_Types;
with GNATCOLL.Terminal;                  use GNATCOLL.Terminal;
with Types;                              use Types;

package Flow_Generated_Globals is

   --  -------------------------------------
   --  -- Flow_Generated_Globals Algorithm --
   --  -------------------------------------
   --
   --  This algorithm is applied to individual compilation units.
   --
   --  During the first pass:
   --
   --    * For every subprogram and task in SPARK a GG graph is created. The
   --      graph is then traversed to classify global variables as proof ins,
   --      ins and outs, and called subprograms as proof only calls, definite
   --      calls and conditional calls. Also we take note of all local
   --      variables. This info is then stored in the ALI file.
   --
   --    * For every subprogram and task that is NOT in SPARK and does NOT
   --      have a user-provided contract only GG entries and not a GG graph is
   --      created and stored in the ALI file. Those GG entries mirror the xref
   --      information that the frontend stores in the ALI file (see also
   --      Spark_Frame_Condition). For these, all subprogram calls are
   --      considered to be conditional calls and all writes to variables are
   --      considered to be read-writes (pure reads are also included in the
   --      reads of course), since the xref information only records 'reads'
   --      and 'writes'.
   --
   --    * For every package all known state abstractions and all their
   --      constituents are collected and this info is stored in the ALI file.
   --
   --    * We collect some data relevant to tasking: a set of nonblocking
   --      subprograms, instance counts, the value of Max_Queue_Length if
   --      present, etc.
   --
   --    * We collect potentially nonreturning subprograms.
   --
   --    * We also collect subprograms with the Terminating annotation.
   --
   --  During the second pass:
   --
   --    * All information stored in the ALI files during the first pass is
   --      read back.
   --
   --    * A Global Graph for the entire compilation unit is created. This
   --      graph contains only subprograms, tasks and variables; it does not
   --      contain abstract states and packages. There are 3 vertices per
   --      subprogram/task that represent the subprogram's proof inputs, inputs
   --      and outputs. Each variable is represented by a vertex.
   --
   --    * We then draw edges between those vertices based on the GG info that
   --      we read from the ALI files. For subprograms that are marked as
   --      SPARK_Mode Off or that contain illegal SPARK constructs we use the
   --      Get_Globals function instead of the GG info from the ALI files.
   --
   --    * Lastly we use the compilation unit's Global Graph and information
   --      that we have about state abstractions and their constituents to
   --      return globals appropriate to the caller's scope.

   --  -------------------------------
   --  -- Generated Globals Section --
   --  -------------------------------
   --
   --  The Generated Globals section is located at the end of the ALI file.
   --
   --  All lines with information related to the Generated Globals start
   --  with a "GG" string, and the rest of the line is a string produced by
   --  the Serialize package.
   --
   --  See type ALI_Entry in the body of this package for details. In
   --  summary we record the following information:
   --
   --  * Abstract States and their constituents
   --  * Remote abstract states
   --  * Variables and subprograms used by subprograms
   --  * Volatile variables and external state abstractions
   --  * Nonblocking subprograms
   --  * Potentially nonreturning subprograms
   --  * Subprograms with the Terminating annotation
   --  * Tasking-related information.
   --    - suspension objects that call suspends on
   --    - protected objects whose entries are called
   --    - protected objects read-locked by function calls
   --    - protected objects write-locked by procedure calls
   --    - accessed unsynchronized objects
   --    - task instances and their number (one or more)
   --    - value of Max_Queue_Length, if present on an entry
   --
   ----------------------------------------------------------------------

   type GG_Mode_T is (GG_No_Mode,
                      GG_Read_Mode,
                      GG_Write_Mode) with Ghost;

   function GG_Mode return GG_Mode_T with Ghost;
   --  Returns the current mode

   type Globals_Origin_T is (Origin_User, Origin_Flow, Origin_Frontend);
   --  User     : Hand-written annotations
   --  Flow     : Produced using flow analysis
   --  Frontend : Produced from the XREF sections of the ALI files

   function Disjoint (A, B, C : Name_Sets.Set) return Boolean;
   --  Returns True iff sets A, B, C are mutually disjoint

   type Call_Names is record
      Proof_Calls       : Name_Sets.Set;  --  Flow
      Conditional_Calls : Name_Sets.Set;  --  Flow
      Definite_Calls    : Name_Sets.Set;  --  Flow/Frontend
   end record
   with Dynamic_Predicate => Disjoint (Call_Names.Proof_Calls,
                                       Call_Names.Conditional_Calls,
                                       Call_Names.Definite_Calls);

   type Flow_Names is record
      Proper  : Global_Names;
      Refined : Global_Names;

      Initializes : Name_Sets.Set;
      --  Only meaningful for packages

      Calls : Call_Names;
   end record;
   --  Information needed to synthesize the Global contract

   type Name_Tasking_Info is array (Tasking_Info_Kind) of Name_Sets.Set;
   --  Tasking objects accessed by a given entity

   type Partial_Contract is record
      Name             : Entity_Name;
      Local            : Boolean;
      Kind             : Entity_Kind;
      Is_Protected     : Boolean;
      Is_Library_Level : Boolean;
      Origin           : Globals_Origin_T;
      Parents          : Name_Lists.List;

      Globals          : Flow_Names;

      Local_Variables  : Name_Sets.Set;

      Tasking          : Name_Tasking_Info;

      Has_Terminate    : Boolean;
      Nonreturning     : Boolean;
      Nonblocking      : Boolean;
   end record;
   --  IMPORTANT: If you add fields to this, make sure to also update the
   --  serialisation procedure (in the body of flow_generated_globals), and
   --  update Null_Partial_Contract.

   ----------------------------------------------------------------------
   --  Protected types instances
   ----------------------------------------------------------------------

   type Priority_Kind is (Nonstatic,
                          Static,
                          Default_Prio,
                          Default_Interrupt_Prio,
                          Last_Interrupt_Prio);
   --  Kind of expression that denotes a protected object priority

   type Priority_Value is record
      Kind  : Priority_Kind;
      Value : Int;
   end record;
   --  Priority of a protected type; Value is only relevant if Kind is Static.
   --  (This should really be a discriminated record but storing such records
   --  in containers is troublesome).

   ----------------------------------------------------------------------
   --  Task types instances
   ----------------------------------------------------------------------

   subtype Instance_Number is Int range -1 .. Int'Last
   with Static_Predicate => Instance_Number /= 0;
   --  For Instances we use type Instance_Number with the following meaning:
   --  * Instances > 0 represents the number of instances that we counted
   --  * Instances = -1 stands for "many" instances, i.e. we are not able to
   --    determine the exact number.

   type Task_Object is
      record
         Name      : Entity_Name;
         Instances : Instance_Number;
         Node      : Node_Id;
      end record;
   --  Task object with the name of the library-level object and task type
   --  instances (which can be many, e.g. for task arrays or records with two
   --  components of a given task type).
   --
   --  Error messages related to a task object will be attached to Node.

private
   Current_Mode : GG_Mode_T := GG_No_Mode with Ghost;

   -------------
   -- GG_Mode --
   -------------

   function GG_Mode return GG_Mode_T is (Current_Mode);

   Term_Info : GNATCOLL.Terminal.Terminal_Info;
   --  For colored debug output; ??? should be global for Flow

   XXX : constant Boolean := False;
   --  Flag to enable debugging of the global generation in both phases
   --  ??? RENAME THIS PLEASE

   Debug_Partial_Contracts : constant Boolean := True and XXX;
   --  Display contracts as they are built

   procedure Debug_Traversal (E : Entity_Id) with Pre => Present (E);
   --  Display order of traversal

   Variable_Input : constant Entity_Name := To_Entity_Name ("__VARIABLE");
   --  ??? unlike in phase 1, we cannot reuse Null_Entity_Id, because it is not
   --  in range of Entity_Name and so it cannot be stored in the containers
   --  based on that type.

end Flow_Generated_Globals;
