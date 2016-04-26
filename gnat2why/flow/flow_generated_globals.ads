------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                 F L O W . G E N E R A T E D _ G L O B A L S              --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--               Copyright (C) 2015-2016, Altran UK Limited                 --
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

with Ada.Containers.Doubly_Linked_Lists;
with Ada.Containers.Hashed_Maps;
with Common_Containers;                  use Common_Containers;
with Flow;                               use Flow;
with Flow_Types;                         use Flow_Types;
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
   --    * We also collect some data relevant to tasking: a set of
   --      nonblocking subprograms, instance counts, etc.
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
   --  * Tasking-related information.
   --    - suspension objects that call suspends on
   --    - protected objects whose entries are called
   --    - protected objects read-locked by function calls
   --    - protected objects write-locked by procedure calls
   --    - accessed unsynchronized objects
   --    - task instances and their number (one or more)
   --
   ----------------------------------------------------------------------

   type GG_Mode_T is (GG_No_Mode,
                      GG_Read_Mode,
                      GG_Write_Mode);

   type Globals_Origin_T is (Origin_User, Origin_Flow, Origin_Frontend);
   --  User     : Hand-written annotations
   --  Flow     : Produced using flow analysis
   --  Frontend : Produced from the XREF sections of the ALI files

   type Global_Phase_1_Info is record
      Name                  : Entity_Name;
      Kind                  : Analyzed_Subject_Kind;
      Globals_Origin        : Globals_Origin_T;
      Inputs_Proof          : Name_Sets.Set; --  Flow/User
      Inputs                : Name_Sets.Set; --  Flow/Frontend/User
      Outputs               : Name_Sets.Set; --  Flow/Frontend/User
      Proof_Calls           : Name_Sets.Set; --  Flow
      Definite_Calls        : Name_Sets.Set; --  Flow
      Conditional_Calls     : Name_Sets.Set; --  Flow/Frontend
      Local_Variables       : Name_Sets.Set; --  Flow
      Local_Subprograms     : Name_Sets.Set; --  Flow
      Local_Definite_Writes : Name_Sets.Set; --  Flow
   end record;
   --  IMPORTANT: If you add fields to this, make sure to also update the
   --  serialisation procedure (in the body of flow_generated_globals), and
   --  update Null_Global_Info below.

   package Global_Info_Lists is new Ada.Containers.Doubly_Linked_Lists
     (Element_Type => Global_Phase_1_Info);

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

   function GG_Mode return GG_Mode_T with Ghost;
   --  Returns the current mode.

   ----------------------------------------------------------------------
   --  Task instances
   ----------------------------------------------------------------------

   type Instance_Number is (One, Many);
   --  Number of task type instances in an object declaration

   type Task_Object is
      record
         Name      : Entity_Name;
         Instances : Instance_Number;
         Node      : Node_Id;
      end record;
   --  Task object with the name of the library-level object and task type
   --  instances (which can be many, e.g. for task arrays or records with
   --  two components of a given task type).
   --
   --  Error messages related to a task object will be attached to Node.

   package Task_Lists is
     new Ada.Containers.Doubly_Linked_Lists (Task_Object);
   --  Containers with task instances

   package Task_Instances_Maps is
     new Ada.Containers.Hashed_Maps (Key_Type        => Entity_Name,
                                     Element_Type    => Task_Lists.List,
                                     Hash            => Name_Hash,
                                     Equivalent_Keys => "=",
                                     "="             => Task_Lists."=");
   --  Containers that map task types to objects with task instances (e.g. task
   --  arrays may contain several instances of a task type and task record may
   --  contain instances of several tasks).

   Task_Instances : Task_Instances_Maps.Map;
   --  Task instances

   type Phase is (GG_Phase_1, GG_Phase_2);

   Tasking_Info_Bag :
     array (Phase, Tasking_Info_Kind) of Name_Graphs.Map :=
     (others => (others => Name_Graphs.Empty_Map));
   --  Maps from subprogram names to accessed objects
   --
   --  In phase 1 it is populated with objects directly accessed by each
   --  subprogram and stored in the ALI file. In phase 2 it is populated
   --  with objects directly and indirectly accessed by each subprogram.

   type Object_Priority is
      record
         Variable : Entity_Name;
         Priority : Priority_Value;
      end record;
   --  Protected object and its priority

   procedure Register_Task_Object
     (Type_Name : Entity_Name;
      Object    : Task_Object);

   ----------------------------------------------------------------------
   --  State information
   ----------------------------------------------------------------------

   State_Comp_Map         : Name_Graphs.Map := Name_Graphs.Empty_Map;
   --  Mapping from abstract states to their constituents, i.e.
   --  abstract_state -> {constituents}

   Comp_State_Map         : Name_Maps.Map   := Name_Maps.Empty_Map;
   --  A reverse of the above mapping, i.e. constituent -> abstract_state,
   --  which speeds up some queries. It is populated at the end of GG_Read from
   --  State_Comp_Map.

   All_State_Abstractions : Name_Sets.Set   := Name_Sets.Empty_Set;
   --  State abstractions that the GG knows of

   Remote_States          : Name_Sets.Set   := Name_Sets.Empty_Set;
   --  State abstractions that are referenced in the current compilation unit
   --  but are declared outside of it.

   ----------------------------------------------------------------------
   --  Volatile information
   ----------------------------------------------------------------------

   All_Volatile_Vars     : Name_Sets.Set := Name_Sets.Empty_Set;
   Async_Writers_Vars    : Name_Sets.Set := Name_Sets.Empty_Set;
   Async_Readers_Vars    : Name_Sets.Set := Name_Sets.Empty_Set;
   Effective_Reads_Vars  : Name_Sets.Set := Name_Sets.Empty_Set;
   Effective_Writes_Vars : Name_Sets.Set := Name_Sets.Empty_Set;
   --  Volatile information

   procedure Add_To_Remote_States (F : Flow_Id);
   --  Processes F and adds it to Remote_States if it is a remote state
   --  abstraction.

   procedure Add_To_Volatile_Sets_If_Volatile (F : Flow_Id);
   --  Processes F and adds it to All_Volatile_Vars, Async_Writers_Vars,
   --  Async_Readers_Vars, Effective_Reads_Vars, or Effective_Writes_Vars
   --  as appropriate.

   procedure Print_Tasking_Info_Bag (P : Phase);
   --  Display the tasking-related information

private

   Current_Mode      : GG_Mode_T := GG_No_Mode with Ghost;

   Current_Comp_Unit : Node_Id;
   --  This node will hold the current compilation unit that is being analyzed.
   --  On phase 1 GG_Write_Initialize is responsible for setting the node.
   --  On phase 2 GG_Read is responsible for setting the node.

   GG_Generated      : Boolean   := False;
   --  Set to True by GG_Read once the Global Graph has been generated.

   -------------
   -- GG_Mode --
   -------------

   function GG_Mode return GG_Mode_T is (Current_Mode);

end Flow_Generated_Globals;
