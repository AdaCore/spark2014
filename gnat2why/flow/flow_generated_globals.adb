------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--               F L O W . C O M P U T E D _ G L O B A L S                  --
--                                                                          --
--                                B o d y                                   --
--                                                                          --
--               Copyright (C) 2014-2015, Altran UK Limited                 --
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

with Ada.Containers.Hashed_Maps;
with Ada.Containers.Hashed_Sets;
with Ada.Strings.Maps;           use Ada.Strings.Maps;
with Ada.Strings.Unbounded;      use Ada.Strings.Unbounded;
with Ada.Text_IO;                use Ada.Text_IO;
with Ada.Text_IO.Unbounded_IO;   use Ada.Text_IO.Unbounded_IO;
with GNAT.Regpat;                use GNAT.Regpat;

with AA_Util;                    use AA_Util;
with ALI;                        use ALI;
with Lib;                        use Lib;
with Lib.Util;                   use Lib.Util;
with Namet;                      use Namet;
with Osint;                      use Osint;
with Osint.C;                    use Osint.C;
with Output;                     use Output;
with Sem_Util;                   use Sem_Util;
with Sinfo;                      use Sinfo;
with Snames;                     use Snames;

with Call;                       use Call;
with Gnat2Why_Args;
with Hashing;                    use Hashing;
with SPARK_Definition;           use SPARK_Definition;
with SPARK_Frame_Conditions;     use SPARK_Frame_Conditions;
with SPARK_Util;                 use SPARK_Util;

with Flow_Debug;                 use Flow_Debug;
with Flow_Utility;               use Flow_Utility;
with Graphs;
with Serialisation;              use Serialisation;

package body Flow_Generated_Globals is

   use type Flow_Id_Sets.Set;
   use type Name_Sets.Set;

   use Name_Graphs;

   subtype GG_Edge_Colours is Edge_Colours range EC_Default .. EC_Default;

   ----------------------------------------------------------------------
   --  Debug flags
   ----------------------------------------------------------------------

   Debug_Print_Info_Sets_Read        : constant Boolean := False;
   --  Enables printing of Subprogram_Info_Sets as read from ALI files

   Debug_Print_Global_Graph          : constant Boolean := True;
   --  Enables printing of the Global_Graph

   Debug_GG_Read_Timing              : constant Boolean := False;
   --  Enables timing information for gg_read

   Debug_Print_Generated_Initializes : constant Boolean := False;
   --  Enables printing of the generated initializes aspects

   Debug_Print_Tasking_Info          : constant Boolean := False;
   --  Enables printing of tasking-related information

   ----------------------------------------------------------------------
   --  Local state
   ----------------------------------------------------------------------

   Subprogram_Info_List        : Global_Info_Lists.List :=
     Global_Info_Lists.Empty_List;
   --  Information about subprograms from the "generated globals" algorithm

   Package_Info_List           : Global_Info_Lists.List :=
     Global_Info_Lists.Empty_List;
   --  Information about packages from the "generated globals" algorithm

   GG_Exists_Cache             : Name_Sets.Set := Name_Sets.Empty_Set;
   --  This should be the equivalent of:
   --     {x.name for all x of Subprogram_Info_List}

   Nonblocking_Subprograms_Set : Name_Sets.Set := Name_Sets.Empty_Set;
   --  Subprograms, entries and tasks that do not contain potentially
   --  blocking statements (but still may call another blocking
   --  subprogram).

   ----------------------------------------------------------------------
   --  State information
   ----------------------------------------------------------------------

   State_Comp_Map : Name_Graphs.Map := Name_Graphs.Empty_Map;
   --  state -> {components}
   --
   --  This maps abstract state to its constituents.

   Comp_State_Map : Name_Maps.Map   := Name_Maps.Empty_Map;
   --  component -> state
   --
   --  This is the reverse of the above, and is filled in at the end of
   --  GG_Read from state_comp_map, in order to speed up some queries.

   ----------------------------------------------------------------------
   --  Initializes information
   ----------------------------------------------------------------------

   type Initializes_Info is record
      LHS       : Name_Sets.Set := Name_Sets.Empty_Set;
      LHS_Proof : Name_Sets.Set := Name_Sets.Empty_Set;
      RHS       : Name_Sets.Set := Name_Sets.Empty_Set;
      RHS_Proof : Name_Sets.Set := Name_Sets.Empty_Set;
   end record;

   package Initializes_Aspects_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Name,
      Element_Type    => Initializes_Info,
      Hash            => Name_Hash,
      Equivalent_Keys => "=");

   Initializes_Aspects_Map : Initializes_Aspects_Maps.Map :=
     Initializes_Aspects_Maps.Empty_Map;

   All_Initialized_Names   : Name_Sets.Set := Name_Sets.Empty_Set;
   --  This set of names will hold all variables and state abstractions
   --  that we know are initialized.

   ----------------------------------------------------------------------
   --  Volatile information
   ----------------------------------------------------------------------

   All_Volatile_Vars     : Name_Sets.Set := Name_Sets.Empty_Set;
   Async_Writers_Vars    : Name_Sets.Set := Name_Sets.Empty_Set;
   Async_Readers_Vars    : Name_Sets.Set := Name_Sets.Empty_Set;
   Effective_Reads_Vars  : Name_Sets.Set := Name_Sets.Empty_Set;
   Effective_Writes_Vars : Name_Sets.Set := Name_Sets.Empty_Set;
   --  Volatile information

   Tasking_Info_Bag : array (Tasking_Info_Kind) of Name_Graphs.Map :=
     (others => Name_Graphs.Empty_Map);
   --  Tasking-related information read from ALI file and then processed

   ----------------------------------------------------------------------
   --  Global_Id
   ----------------------------------------------------------------------

   type Global_Id_Kind is (Null_Kind,
                           --  Does not represent anything yet

                           Subprogram_Kind,
                           --  This kind should only be used in Local_Graphs

                           Ins_Kind,
                           --  Represents subprogram's Ins

                           Outs_Kind,
                           --  Represents subprogram's Outs

                           Proof_Ins_Kind,
                           --  Represents subprogram's Proof_Ins

                           Variable_Kind
                           --  Represents a global variable
                          );

   type Global_Id (Kind : Global_Id_Kind := Null_Kind) is record
      case Kind is
         when Null_Kind =>
            null;

         when others =>
            Name : Entity_Name;
      end case;
   end record;

   Null_Global_Id : constant Global_Id := Global_Id'(Kind => Null_Kind);

   function Global_Hash (X : Global_Id) return Ada.Containers.Hash_Type
   is (if X.Kind = Null_Kind
       then Generic_Integer_Hash (-1)
       else Name_Hash (X.Name));

   --------------------
   -- Tasking graphs --
   --------------------

   package Entity_Name_Graphs is new Graphs
     (Vertex_Key   => Entity_Name,
      Edge_Colours => GG_Edge_Colours,
      Null_Key     => Null_Entity_Name,
      Key_Hash     => Name_Hash,
      Test_Key     => "=");

   Tasking_Graph : array (Tasking_Info_Kind) of Entity_Name_Graphs.Graph :=
     (others => Entity_Name_Graphs.Create);
   --  Graphs with information about objects accessed by subprograms

   Call_Graph : Entity_Name_Graphs.Graph := Entity_Name_Graphs.Create;
   --  Call graph where vertices correspond to subprograms and edges correspond
   --  to subprogram calls. Subprogram calls are provided by the front end,
   --  i.e. they are not affected by user's annotations. Unlike Global_Graph,
   --  it contains no objects.

   type Name_Tasking_Info is array (Tasking_Info_Kind) of Name_Sets.Set;
   --  Similar to Tasking_Info, but with name sets.

   use type Entity_Name_Graphs.Vertex_Id;

   -------------------
   -- Global_Graphs --
   -------------------

   package Global_Graphs is new Graphs
     (Vertex_Key   => Global_Id,
      Key_Hash     => Global_Hash,
      Edge_Colours => GG_Edge_Colours,
      Null_Key     => Null_Global_Id,
      Test_Key     => "=");

   package Vertex_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Global_Graphs.Vertex_Id,
      Hash                => Global_Graphs.Vertex_Hash,
      Equivalent_Elements => Global_Graphs."=",
      "="                 => Global_Graphs."=");

   Local_Graph  : Global_Graphs.Graph;
   --  This graph will represent the hierarchy of subprograms (which
   --  subprogram is nested in which one) and will be used to determine
   --  which local variables can act as globals to which subprograms.

   Global_Graph : Global_Graphs.Graph;
   --  This graph will represent the globals that each subprogram has as
   --  inputs, outputs and proof inputs.

   ---------------------------------------------------
   -- Regular expression for predefined subprograms --
   ---------------------------------------------------

   --  Any user-defined subprogram for which we do not know its blocking status
   --  (e.g. when its body is missing or is not in SPARK) is assumed to be
   --  potentially blocking. For predefined subprograms we never read their
   --  blocking status from ALI file, but assume that they are nonblocking.
   --  This assumption is valid, because user-defined subprograms that call a
   --  predefined potentially blocking subprogram have been already marked as
   --  potentially blocking.
   --
   --  However, here we still need to distinguish between user-defined and
   --  predefined subprograms and can only do this by their Entity_Name (i.e.
   --  string). This is done with regular expressions, which more efficient
   --  than naive string matching. The regexp is a global constant and so it
   --  is compiled only once.

   Predefined : constant Pattern_Matcher :=
     Compile ("^(ada|interfaces|system)__");
   --  Regexp for predefined entities

   ----------------------------------------------------------------------
   --  Serialisation
   ----------------------------------------------------------------------

   type ALI_Entry_Kind is (EK_Error,
                           EK_End_Marker,
                           EK_State_Map,
                           EK_Volatiles,
                           EK_Globals,
                           EK_Tasking_Instance_Count,
                           EK_Tasking_Info,
                           EK_Tasking_Nonblocking);

   type ALI_Entry (Kind : ALI_Entry_Kind := EK_Error) is record
      case Kind is
         when EK_Error | EK_End_Marker =>
            null;
         when EK_State_Map =>
            The_State                   : Entity_Name;
            The_Constituents            : Name_Sets.Set;
         when EK_Volatiles =>
            All_Async_Readers           : Name_Sets.Set;
            All_Async_Writers           : Name_Sets.Set;
            All_Effective_Reads         : Name_Sets.Set;
            All_Effective_Writes        : Name_Sets.Set;
         when EK_Globals =>
            The_Global_Info             : Global_Phase_1_Info;
         when EK_Tasking_Instance_Count =>
            The_Type                    : Entity_Name;
            The_Count                   : Instance_Number;
         when EK_Tasking_Info =>
            The_Entity                  : Entity_Name;
            The_Tasking_Info            : Name_Tasking_Info;
         when EK_Tasking_Nonblocking =>
            The_Nonblocking_Subprograms : Name_Sets.Set;
      end case;
   end record;
   --  IMPORTANT: If you change this, please also remember to update the
   --  serialisation procedure, and Null_ALI_Entry to initialize any
   --  scalars.

   Null_ALI_Entry : constant array (ALI_Entry_Kind) of ALI_Entry := (
      EK_Error                  => (Kind => EK_Error),

      EK_End_Marker             => (Kind => EK_End_Marker),

      EK_State_Map              => (Kind      => EK_State_Map,
                                    The_State => Null_Entity_Name,
                                    others    => <>),

      EK_Volatiles              => (Kind   => EK_Volatiles,
                                    others => <>),

      EK_Globals                => (Kind            => EK_Globals,
                                    The_Global_Info => Null_Global_Info),

      EK_Tasking_Instance_Count => (Kind       => EK_Tasking_Instance_Count,
                                    The_Type   => Null_Entity_Name,
                                    The_Count  => Instance_Number'First),

      EK_Tasking_Info           => (Kind       => EK_Tasking_Info,
                                    The_Entity => Null_Entity_Name,
                                    others     => <>),

      EK_Tasking_Nonblocking    => (Kind   => EK_Tasking_Nonblocking,
                                    others => <>)
   );

   procedure Serialize (A : in out Archive; V : in out Entity_Name);

   procedure Serialize is new Serialize_Set
     (T              => Name_Sets.Set,
      E              => Entity_Name,
      Cursor         => Name_Sets.Cursor,
      Null_Container => Name_Sets.Empty_Set,
      Null_Element   => Null_Entity_Name,
      First          => Name_Sets.First,
      Next           => Name_Sets.Next,
      Has_Element    => Name_Sets.Has_Element,
      Element        => Name_Sets.Element,
      Insert         => Name_Sets.Insert);

   procedure Serialize (A : in out Archive; V : in out Name_Tasking_Info);

   procedure Serialize (A : in out Archive; V : in out Global_Phase_1_Info);

   procedure Serialize (A : in out Archive; V : in out ALI_Entry);

   ---------------
   -- Serialize --
   ---------------

   procedure Serialize (A : in out Archive; V : in out Entity_Name) is
      S : Unbounded_String;
   begin
      if A.Kind = Serialisation.Output then
         S := To_Unbounded_String (To_String (V));
      end if;
      Serialize (A, S);
      if A.Kind = Serialisation.Input then
         V := To_Entity_Name (To_String (S));
      end if;
   end Serialize;

   procedure Serialize (A : in out Archive; V : in out Name_Tasking_Info) is
   begin
      for Kind in Tasking_Info_Kind loop
         Serialize (A, V (Kind), Kind'Img);
      end loop;
   end Serialize;

   procedure Serialize (A : in out Archive; V : in out Global_Phase_1_Info) is
      procedure Serialize is new Serialisation.Serialize_Discrete
        (T => Analyzed_Subject_Kind);
      procedure Serialize is new Serialisation.Serialize_Discrete
        (T => Globals_Origin_T);
   begin
      Serialize (A, V.Name);
      Serialize (A, V.Kind);
      Serialize (A, V.Globals_Origin);
      Serialize (A, V.Inputs_Proof,          "var_proof");
      Serialize (A, V.Inputs,                "var_in");
      Serialize (A, V.Outputs,               "var_out");
      Serialize (A, V.Proof_Calls,           "calls_proof");
      Serialize (A, V.Definite_Calls,        "calls");
      Serialize (A, V.Conditional_Calls,     "calls_conditional");
      Serialize (A, V.Local_Variables,       "local_var");
      Serialize (A, V.Local_Subprograms,     "local_sub");
      Serialize (A, V.Local_Definite_Writes, "local_init");
   end Serialize;

   procedure Serialize (A : in out Archive; V : in out ALI_Entry) is
      procedure Serialize is new Serialisation.Serialize_Discrete
        (T => ALI_Entry_Kind);
      procedure Serialize is new Serialisation.Serialize_Discrete
        (T => Instance_Number);

      Kind : ALI_Entry_Kind := ALI_Entry_Kind'First;
   begin
      if A.Kind = Serialisation.Output then
         Kind := V.Kind;
      end if;
      Serialize (A, Kind);
      if A.Kind = Serialisation.Input then
         V := Null_ALI_Entry (Kind);
      end if;

      case V.Kind is
         when EK_Error =>
            raise Program_Error;

         when EK_End_Marker =>
            null;

         when EK_State_Map =>
            Serialize (A, V.The_State);
            Serialize (A, V.The_Constituents);

         when EK_Volatiles =>
            Serialize (A, V.All_Async_Readers,    "AR");
            Serialize (A, V.All_Async_Writers,    "AW");
            Serialize (A, V.All_Effective_Reads,  "ER");
            Serialize (A, V.All_Effective_Writes, "EW");

         when EK_Globals =>
            Serialize (A, V.The_Global_Info);

         when EK_Tasking_Instance_Count =>
            Serialize (A, V.The_Type);
            Serialize (A, V.The_Count);

         when EK_Tasking_Info =>
            Serialize (A, V.The_Entity);
            Serialize (A, V.The_Tasking_Info);

         when EK_Tasking_Nonblocking =>
            Serialize (A, V.The_Nonblocking_Subprograms);
      end case;

   exception
      when Serialisation.Parse_Error =>
         pragma Assert (A.Kind = Serialisation.Input);
         V := (Kind => EK_Error);
   end Serialize;

   ----------------------------------------------------------------------
   --  Local subprograms
   ----------------------------------------------------------------------

   procedure Add_To_Volatile_Sets_If_Volatile (F : Flow_Id);
   --  Processes F and adds it to All_Volatile_Vars, Async_Writers_Vars,
   --  Async_Readers_Vars, Effective_Reads_Vars, or Effective_Writes_Vars
   --  as appropriate

   procedure Print_Global_Phase_1_Info (Info : Global_Phase_1_Info);
   --  Prints all global related info of an entity

   procedure Print_Global_Graph (Filename : String;
                                 G        : Global_Graphs.Graph);
   --  Writes dot and pdf files for the Global_Graph

   procedure Print_Generated_Initializes_Aspects;
   --  Prints all the generated initializes aspects

   procedure Print_Name_Set (Header : String; Set : Name_Sets.Set);
   --  Print Header followed by elements of Set

   --------------------
   -- Print_Name_Set --
   --------------------

   procedure Print_Name_Set (Header : String; Set : Name_Sets.Set) is
   begin
      Write_Line (Header);
      for Name of Set loop
         Write_Line ("   " & To_String (Name));
         --  ??? use Indent/Outdent instead of fixed amount of spaces
      end loop;
   end Print_Name_Set;

   procedure GG_Get_MR_Globals (EN          : Entity_Name;
                                Proof_Reads : out Name_Sets.Set;
                                Reads       : out Name_Sets.Set;
                                Writes      : out Name_Sets.Set);
   --  Gets the most refined proof reads, reads and writes globals of EN

   procedure Up_Project
     (Most_Refined      : Name_Sets.Set;
      Final_View        : out Name_Sets.Set;
      Scope             : Flow_Scope;
      Reads             : in out Flow_Id_Sets.Set;
      Processing_Writes : Boolean := False);
   --  Distinguishes between simple vars and constituents. For constituents, it
   --  checks if they are visible and if they are NOT we check if their
   --  enclosing state is. If the enclosing state is visible then return that
   --  (otherwise repeat the process). When Processing_Writes is set, we also
   --  check if all constituents are used and if they are not we also add them
   --  on the Reads set.

   ----------------------------------------------------------------------

   --------------------------------------
   -- Add_To_Volatile_Sets_If_Volatile --
   --------------------------------------

   procedure Add_To_Volatile_Sets_If_Volatile (F : Flow_Id) is
      N : Entity_Name;
   begin
      case F.Kind is
         when Direct_Mapping | Record_Field =>
            N := To_Entity_Name (Get_Direct_Mapping_Id (F));
         when others =>
            return;
      end case;

      if Is_Volatile (F) then
         All_Volatile_Vars.Include (N);

         if Has_Async_Readers (F) then
            Async_Readers_Vars.Include (N);

            if Has_Effective_Writes (F) then
               Effective_Writes_Vars.Include (N);
            end if;
         end if;

         if Has_Async_Writers (F) then
            Async_Writers_Vars.Include (N);

            if Has_Effective_Reads (F) then
               Effective_Reads_Vars.Include (N);
            end if;
         end if;
      end if;
   end Add_To_Volatile_Sets_If_Volatile;

   -------------------------------
   -- Print_Global_Phase_1_Info --
   -------------------------------

   procedure Print_Global_Phase_1_Info (Info : Global_Phase_1_Info) is
   begin
      Write_Line ((case Info.Kind is
                   when Kind_Subprogram                  => "Subprogram ",
                   when Kind_Entry                       => "Entry ",
                   when Kind_Task                        => "Task ",
                   when Kind_Package | Kind_Package_Body => "Package ")
        & To_String (Info.Name));

      Print_Name_Set ("Proof_Ins            :", Info.Inputs_Proof);
      Print_Name_Set ("Inputs               :", Info.Inputs);
      Print_Name_Set ("Outputs              :", Info.Outputs);
      Print_Name_Set ("Proof calls          :", Info.Proof_Calls);
      Print_Name_Set ("Definite calls       :", Info.Definite_Calls);
      Print_Name_Set ("Conditional calls    :", Info.Conditional_Calls);
      Print_Name_Set ("Local variables      :", Info.Local_Variables);

      if Info.Kind in Kind_Package | Kind_Package_Body then
         Print_Name_Set ("Local definite writes:", Info.Local_Definite_Writes);
      end if;
   end Print_Global_Phase_1_Info;

   ------------------------
   -- Print_Global_Graph --
   ------------------------

   procedure Print_Global_Graph (Filename : String;
                                 G        : Global_Graphs.Graph)
   is
      use Global_Graphs;

      function NDI
        (G : Graph;
         V : Vertex_Id)
         return Node_Display_Info;
      --  Pretty-printing for each vertex in the dot output

      function EDI
        (G      : Graph;
         A      : Vertex_Id;
         B      : Vertex_Id;
         Marked : Boolean;
         Colour : GG_Edge_Colours)
         return Edge_Display_Info;
      --  Pretty-printing for each edge in the dot output

      ---------
      -- NDI --
      ---------

      function NDI
        (G : Graph;
         V : Vertex_Id) return Node_Display_Info
      is
         G_Id  : constant Global_Id := G.Get_Key (V);

         Shape : constant Node_Shape_T := (if G_Id.Kind = Variable_Kind
                                           then Shape_Oval
                                           else Shape_Box);

         Label : constant String :=
           (case G_Id.Kind is
              when Subprogram_Kind => "Subprogram " & To_String (G_Id.Name),
              when Proof_Ins_Kind  => To_String (G_Id.Name) & "'Proof_Ins",
              when Ins_Kind        => To_String (G_Id.Name) & "'Ins",
              when Outs_Kind       => To_String (G_Id.Name) & "'Outs",
              when Variable_Kind   => To_String (G_Id.Name),
              when Null_Kind       => raise Program_Error);

         Rv : constant Node_Display_Info := Node_Display_Info'
           (Show        => True,
            Shape       => Shape,
            Colour      => Null_Unbounded_String,
            Fill_Colour => Null_Unbounded_String,
            Label       => To_Unbounded_String (Label));
      begin
         return Rv;
      end NDI;

      ---------
      -- EDI --
      ---------

      function EDI
        (G      : Graph;
         A      : Vertex_Id;
         B      : Vertex_Id;
         Marked : Boolean;
         Colour : GG_Edge_Colours)
         return Edge_Display_Info
      is
         pragma Unreferenced (G, A, B, Marked, Colour);

         Rv : constant Edge_Display_Info :=
           Edge_Display_Info'(Show   => True,
                              Shape  => Edge_Normal,
                              Colour => Null_Unbounded_String,
                              Label  => Null_Unbounded_String);
      begin
         return Rv;
      end EDI;

   begin
      if Gnat2Why_Args.Debug_Mode then
         if Gnat2Why_Args.Flow_Advanced_Debug then
            G.Write_Pdf_File
              (Filename  => Filename,
               Node_Info => NDI'Access,
               Edge_Info => EDI'Access);
         else
            G.Write_Dot_File
              (Filename  => Filename,
               Node_Info => NDI'Access,
               Edge_Info => EDI'Access);
         end if;
      end if;
   end Print_Global_Graph;

   -----------------------------------------
   -- Print_Generated_Initializes_Aspects --
   -----------------------------------------

   procedure Print_Generated_Initializes_Aspects is
   begin
      Write_Line ("Synthesized initializes aspects:");
      for Init in Initializes_Aspects_Map.Iterate loop
         declare
            Pkg : constant Entity_Name         :=
              Initializes_Aspects_Maps.Key (Init);

            II  : constant Initializes_Info :=
              Initializes_Aspects_Maps.Element (Init);
         begin
            Indent;
            Write_Line ("Package " & To_String (Pkg)  & ":");
            Indent;
            Print_Name_Set ("LHS      : ", II.LHS);
            Print_Name_Set ("LHS_Proof: ", II.LHS_Proof);
            Print_Name_Set ("RHS      : ", II.RHS);
            Print_Name_Set ("RHS_Proof: ", II.RHS_Proof);
            Outdent;
            Outdent;
         end;
      end loop;
   end Print_Generated_Initializes_Aspects;

   ----------------
   -- Up_Project --
   ----------------

   procedure Up_Project
     (Most_Refined      : Name_Sets.Set;
      Final_View        : out Name_Sets.Set;
      Scope             : Flow_Scope;
      Reads             : in out Flow_Id_Sets.Set;
      Processing_Writes : Boolean := False)
   is
      Abstract_States : Name_Sets.Set := Name_Sets.Empty_Set;
   begin
      --  Initializing Final_View to empty
      Final_View := Name_Sets.Empty_Set;

      for N of Most_Refined loop
         if GG_Enclosing_State (N) /= Null_Entity_Name
           and then (No (Find_Entity (N))
                       or else not Is_Visible (Find_Entity (N), Scope))
         then
            declare
               Var               : Entity_Name :=
                 (if Present (Find_Entity (N))
                    and then Is_Visible (Find_Entity (N), Scope)
                  then N
                  else GG_Enclosing_State (N));
               ES                : Entity_Name := GG_Enclosing_State (N);
               Is_Abstract_State : Boolean     :=
                 No (Find_Entity (N))
                   or else not Is_Visible (Find_Entity (N), Scope);
            begin
               while No (Find_Entity (ES))
                 or else not Is_Visible (Find_Entity (ES), Scope)
               loop
                  Is_Abstract_State := True;
                  Var := ES;

                  if GG_Enclosing_State (ES) /= Null_Entity_Name then
                     ES := GG_Enclosing_State (ES);
                  else
                     --  We cannot go any further up and we still do not have
                     --  visibility of the variable or state abstraction that
                     --  we are making use of. This means that the user has
                     --  neglected to provide some state abstraction and the
                     --  refinement thereof. Unfortunately, we might now refer
                     --  to a variable or state that the caller should not have
                     --  vision of.
                     exit;
                  end if;
               end loop;

               Final_View.Include (Var);

               --  We add the enclosing abstract state that we just added to
               --  the Final_View set to the Abstract_States set.
               if Is_Abstract_State then
                  Abstract_States.Include (Var);
               end if;
            end;
         else
            --  Add variables that are directly visible or do not belong to any
            --  state abstraction to the Final_View set.
            Final_View.Include (N);
         end if;
      end loop;

      --  If we Write some but not all constituents of a state abstraction then
      --  this state abstraction is also a Read.
      if Processing_Writes then
         for AS of Abstract_States loop
            declare
               Constituents : constant Name_Sets.Set := GG_Fully_Refine (AS);
            begin
               if not (for all C of Constituents => Most_Refined.Contains (C))
               then
                  Reads.Include (Get_Flow_Id (AS, In_View, Scope));
               end if;
            end;
         end loop;
      end if;
   end Up_Project;

   -------------------------
   -- GG_Write_Initialize --
   -------------------------

   procedure GG_Write_Initialize is
   begin
      --  Open output library info for writing
      Open_Output_Library_Info;

      --  Set mode to writing mode
      Current_Mode := GG_Write_Mode;
   end GG_Write_Initialize;

   -------------------------
   -- GG_Write_State_Info --
   -------------------------

   procedure GG_Write_State_Info (DM : Dependency_Maps.Map) is
   begin
      for S in DM.Iterate loop
         declare
            State_F      : constant Flow_Id := Dependency_Maps.Key (S);

            State_N      : constant Entity_Name :=
              To_Entity_Name (Get_Direct_Mapping_Id (State_F));

            Constituents : constant Name_Sets.Set :=
              To_Name_Set (To_Node_Set (Dependency_Maps.Element (S)));
         begin
            --  Insert new state info into State_Comp_Map.
            State_Comp_Map.Insert (State_N, Constituents);

            --  Check if State_F if volatile and if it is then add it on
            --  the appropriate sets.
            Add_To_Volatile_Sets_If_Volatile (State_F);
         end;
      end loop;
   end GG_Write_State_Info;

   --------------------------
   -- GG_Write_Global_Info --
   --------------------------

   procedure GG_Write_Global_Info (GI : Global_Phase_1_Info) is
      procedure Process_Volatiles (NS : Name_Sets.Set);
      --  Goes through NS, finds volatiles and stores them in the
      --  appropriate sets based on their properties.

      ------------------------
      -- Processs_Volatiles --
      ------------------------

      procedure Process_Volatiles (NS : Name_Sets.Set) is
      begin
         for Name of NS loop
            declare
               E : constant Entity_Id := Find_Entity (Name);
            begin
               if Present (E) then
                  Add_To_Volatile_Sets_If_Volatile (Direct_Mapping_Id (E));
               end if;
            end;
         end loop;
      end Process_Volatiles;

   --  Start of processing for GG_Write_Global_Info

   begin
      case GI.Kind is
         when Kind_Subprogram | Kind_Task | Kind_Entry =>
            Subprogram_Info_List.Append (GI);

         when Kind_Package | Kind_Package_Body =>
            Package_Info_List.Append (GI);
      end case;
      GG_Exists_Cache.Insert (GI.Name);

      --  Gather and save volatile variables
      Process_Volatiles (GI.Inputs_Proof);
      Process_Volatiles (GI.Inputs);
      Process_Volatiles (GI.Outputs);
      Process_Volatiles (GI.Local_Variables);
   end GG_Write_Global_Info;

   -----------------------------
   -- GG_Register_Nonblocking --
   -----------------------------

   procedure GG_Register_Nonblocking (EN : Entity_Name) is
   begin
      Nonblocking_Subprograms_Set.Insert (EN);
   end GG_Register_Nonblocking;

   ------------------------------
   -- GG_Register_Tasking_Info --
   ------------------------------

   procedure GG_Register_Tasking_Info (EN : Entity_Name;
                                       TI : Tasking_Info)
   is
   begin
      for Kind in Tasking_Info_Kind loop
         Tasking_Info_Bag (Kind).Insert (EN, To_Name_Set (TI (Kind)));
      end loop;
   end GG_Register_Tasking_Info;

   -----------------------
   -- GG_Write_Finalize --
   -----------------------

   procedure GG_Write_Finalize
   is
      procedure Write_To_ALI (V : in out ALI_Entry);
      --  Helper subprogram to write the given entry to the ALI file.
      --  Second parameter has to be in out because of the way serialize
      --  works.

      ------------------
      -- Write_To_ALI --
      ------------------

      procedure Write_To_ALI (V : in out ALI_Entry) is
         A : Archive (Serialisation.Output);
      begin
         Serialize (A, V);
         Write_Info_Str ("GG " & To_String (To_String (A)));
         Write_Info_Terminate;
      end Write_To_ALI;

      V : ALI_Entry;
   begin
      --  Write State info
      for C in State_Comp_Map.Iterate loop
         V := (Kind             => EK_State_Map,
               The_State        => Key (C),
               The_Constituents => Element (C));
         Write_To_ALI (V);
      end loop;

      --  Write globals for package and subprograms/tasks
      for Info of Package_Info_List loop
         V := (Kind            => EK_Globals,
               The_Global_Info => Info);
         Write_To_ALI (V);
      end loop;

      for Info of Subprogram_Info_List loop
         V := (Kind            => EK_Globals,
               The_Global_Info => Info);
         Write_To_ALI (V);
      end loop;

      --  Write Volatile info
      V := (Kind                 => EK_Volatiles,
            All_Async_Readers    => Async_Readers_Vars,
            All_Async_Writers    => Async_Writers_Vars,
            All_Effective_Reads  => Effective_Reads_Vars,
            All_Effective_Writes => Effective_Writes_Vars);
      Write_To_ALI (V);

      --  Write nonblocking subprograms
      V := (Kind                        => EK_Tasking_Nonblocking,
            The_Nonblocking_Subprograms => Nonblocking_Subprograms_Set);
      Write_To_ALI (V);

      --  Write tasking-related information. This is a bit awkward since we
      --  need to rotate the information in Tasking_Info_Bag.
      declare
         All_Names : Name_Sets.Set := Name_Sets.Empty_Set;
      begin
         for Kind in Tasking_Info_Kind loop
            for C in Tasking_Info_Bag (Kind).Iterate loop
               All_Names.Include (Key (C));
            end loop;
         end loop;
         for Name of All_Names loop
            V := (Kind             => EK_Tasking_Info,
                  The_Entity       => Name,
                  The_Tasking_Info => <>);
            for Kind in Tasking_Info_Kind loop
               V.The_Tasking_Info (Kind) := Tasking_Objects (Kind, Name);
            end loop;
            Write_To_ALI (V);
         end loop;
      end;

      for C in Task_Instances.Iterate loop
         V := (Kind      => EK_Tasking_Instance_Count,
               The_Type  => Task_Instances_Maps.Key (C),
               The_Count => Task_Instances_Maps.Element (C));
         Write_To_ALI (V);
      end loop;

      --  Write the finalization string.
      V := (Kind => EK_End_Marker);
      Write_To_ALI (V);

      --  Close file and put the package out of writing mode.
      Close_Output_Library_Info;
      Current_Mode := GG_No_Mode;
   end GG_Write_Finalize;

   -------------
   -- GG_Read --
   -------------

   procedure GG_Read (GNAT_Root : Node_Id) is
      All_Globals           : Name_Sets.Set := Name_Sets.Empty_Set;
      --  Contains all global variables

      GG_Subprograms        : Name_Sets.Set := Name_Sets.Empty_Set;
      --  Contains all subprograms for which a GG entry exists

      All_Subprograms       : Name_Sets.Set := Name_Sets.Empty_Set;
      --  Contains all subprograms that we know of, even if a
      --  GG entry does not exist for them.

      All_Other_Subprograms : Name_Sets.Set := Name_Sets.Empty_Set;
      --  Contains all subprograms for which a GG entry does not exist
      --  ??? rename to No_GG_Subprograms?

      procedure Add_All_Edges;
      --  Reads the populated Subprogram_Info_List and generates all the edges
      --  of the Global_Graph. While adding edges we consult the Local_Graph so
      --  as not to add edges to local variables.
      --  It also created edges for (conditional and unconditional) subprogram
      --  calls in the Tasking_Graph.

      procedure Create_All_Vertices;
      --  Creates all the vertices of the Global_Graph and subprogram vertices
      --  in the Tasking_Graph.

      procedure Create_Local_Graph;
      --  Creates the Local_Graph. This graph will be used to prevent adding
      --  edges to local variables on the Global_Graph.

      procedure Create_Tasking_Graph;
      --  Creates graph with tasking-related information; it will contain:
      --  * a vertex for each subprogram that accesses a tasking object,
      --  * a vertex for each tasking object,
      --  * an edge from such subprogram to such vertex.

      procedure Edit_Proof_Ins;
      --  A variable cannot be simultaneously a Proof_In and an Input
      --  of a subprogram. In this case we need to remove the Proof_In
      --  edge. Furthermore, a variable cannot be simultaneously a
      --  Proof_In and an Output (but not an input). In this case we
      --  need to change the Proof_In variable into an Input.

      procedure Generate_Initializes_Aspects;
      --  Once the global graph has been generated, we use it to generate
      --  the initializes aspects.

      procedure Load_GG_Info_From_ALI (ALI_File_Name : File_Name_Type);
      --  Loads the GG info from an ALI file and stores them in the
      --  Subprogram_Info_List, State_Comp_Map and volatile info sets.

      procedure Remove_Constants_Without_Variable_Input;
      --  Removes edges leading to constants without variable input

      procedure Print_Tasking_Info_Bag;
      --  Display the tasking-related information

      procedure Process_Tasking_Graph;
      --  Do transitive closure of the tasking graph and put the resulting
      --  information back to bag with tasking-related information.

      -------------------
      -- Add_All_Edges --
      -------------------

      procedure Add_All_Edges is
         use Global_Graphs;

         G_Ins, G_Outs, G_Proof_Ins : Global_Id;

         function Edge_Selector (A, B : Vertex_Id) return Boolean;
         --  Check if we should add the given edge to the graph based
         --  wheather it is in the local graph or not.

         -------------------
         -- Edge_Selector --
         -------------------

         function Edge_Selector (A, B : Vertex_Id) return Boolean is
            Key_A :          Global_Id := Global_Graph.Get_Key (A);
            Key_B : constant Global_Id := Global_Graph.Get_Key (B);
         begin
            if Key_B.Kind /= Variable_Kind
              or else not (Key_A.Kind in Proof_Ins_Kind |
                             Ins_Kind       |
                             Outs_Kind)
            then
               --  We only need to consult the Local_Graph when attempting
               --  to establish a link between a subprogram and a variable.
               return True;
            end if;

            --  Convert kind so that it can be used on Local_Graph
            Key_A := Global_Id'(Kind => Subprogram_Kind,
                                Name => Key_A.Name);

            if Local_Graph.Get_Vertex (Key_A) = Null_Vertex
              or else Local_Graph.Get_Vertex (Key_B) = Null_Vertex
            then
               return True;
            end if;

            --  Check if local variable B can act as global of subprogram A
            return Local_Graph.Edge_Exists (Key_B, Key_A);
         end Edge_Selector;

      --  Start of processing for Add_All_Edges

      begin

         --  Go through the Subprogram_Info_List and add edges
         for Info of Subprogram_Info_List loop
            G_Ins       := Global_Id'(Kind => Ins_Kind,
                                      Name => Info.Name);

            G_Outs      := Global_Id'(Kind => Outs_Kind,
                                      Name => Info.Name);

            G_Proof_Ins := Global_Id'(Kind => Proof_Ins_Kind,
                                      Name => Info.Name);

            --  Connect the subprogram's Proof_In variables to the
            --  subprogram's Proof_Ins vertex.
            for Input_Proof of Info.Inputs_Proof loop
               Global_Graph.Add_Edge (G_Proof_Ins,
                                      Global_Id'(Kind => Variable_Kind,
                                                 Name => Input_Proof));
            end loop;

            --  Connect the subprogram's Input variables to the
            --  subprogram's Ins vertex.
            for Input of Info.Inputs loop
               Global_Graph.Add_Edge (G_Ins,
                                      Global_Id'(Kind => Variable_Kind,
                                                 Name => Input));
            end loop;

            --  Connect the subprogram's Output variables to the
            --  subprogram's Outputs vertex.
            for Output of Info.Outputs loop
               Global_Graph.Add_Edge (G_Outs,
                                      Global_Id'(Kind => Variable_Kind,
                                                 Name => Output));
            end loop;

            --  Connect the subprogram's Proof_Ins vertex to the
            --  callee's Ins and Proof_Ins vertices.
            for Proof_Call of Info.Proof_Calls loop
               Global_Graph.Add_Edge (G_Proof_Ins,
                                      Global_Id'(Kind => Proof_Ins_Kind,
                                                 Name => Proof_Call));

               Global_Graph.Add_Edge (G_Proof_Ins,
                                      Global_Id'(Kind => Ins_Kind,
                                                 Name => Proof_Call));
            end loop;

            --  Connect the subprogram's Proof_Ins, Ins and Outs
            --  vertices respectively to the callee's Proof_Ins, Ins
            --  and Outs vertices.
            for Definite_Call of Info.Definite_Calls loop
               Global_Graph.Add_Edge (G_Proof_Ins,
                                      Global_Id'(Kind => Proof_Ins_Kind,
                                                 Name => Definite_Call));

               Global_Graph.Add_Edge (G_Ins,
                                      Global_Id'(Kind => Ins_Kind,
                                                 Name => Definite_Call));

               Global_Graph.Add_Edge (G_Outs,
                                      Global_Id'(Kind => Outs_Kind,
                                                 Name => Definite_Call));

               --  Also record the call in the tasking-info graphs
               for Kind in Tasking_Info_Kind loop
                  Tasking_Graph (Kind).Add_Edge (Info.Name,
                                                 Definite_Call);
               end loop;
            end loop;

            --  As above but also add an edge from the subprogram's
            --  Ins vertex to the callee's Outs vertex.
            for Conditional_Call of Info.Conditional_Calls loop
               Global_Graph.Add_Edge (G_Proof_Ins,
                                      Global_Id'(Kind => Proof_Ins_Kind,
                                                 Name => Conditional_Call));

               Global_Graph.Add_Edge (G_Ins,
                                      Global_Id'(Kind => Ins_Kind,
                                                 Name => Conditional_Call));

               Global_Graph.Add_Edge (G_Ins,
                                      Global_Id'(Kind => Outs_Kind,
                                                 Name => Conditional_Call));

               Global_Graph.Add_Edge (G_Outs,
                                      Global_Id'(Kind => Outs_Kind,
                                                 Name => Conditional_Call));

               --  Also record the call in the tasking-info graphs
               for Kind in Tasking_Info_Kind loop
                  Tasking_Graph (Kind).Add_Edge (Info.Name,
                                                 Conditional_Call);
               end loop;
            end loop;
         end loop;

         --  Add edges between subprograms and variables coming from
         --  the Get_Globals function.
         for N of All_Other_Subprograms loop
            declare
               Subprogram   : constant Entity_Id := Find_Entity (N);
               G_Proof_Ins  : Global_Id;
               G_Ins        : Global_Id;
               G_Outs       : Global_Id;
               FS_Proof_Ins : Flow_Id_Sets.Set;
               FS_Reads     : Flow_Id_Sets.Set;
               FS_Writes    : Flow_Id_Sets.Set;

               procedure Add_Edges_For_FS
                 (FS   : Flow_Id_Sets.Set;
                  From : Global_Id);
               --  Adds an edge from From to every Flow_Id in FS

               ----------------------
               -- Add_Edges_For_FS --
               ----------------------

               procedure Add_Edges_For_FS
                 (FS   : Flow_Id_Sets.Set;
                  From : Global_Id)
               is
                  G   : Global_Id;
                  Nam : Entity_Name;
               begin
                  for F of FS loop
                     Nam := (if F.Kind in Direct_Mapping |
                                          Record_Field
                             then
                                To_Entity_Name (Get_Direct_Mapping_Id (F))
                             elsif F.Kind = Magic_String then
                                F.Name
                             else
                                raise Program_Error);
                     G   := Global_Id'(Kind => Variable_Kind,
                                       Name => Nam);

                     if not Global_Graph.Edge_Exists (From, G) then
                        Global_Graph.Add_Edge (From, G);
                     end if;
                  end loop;
               end Add_Edges_For_FS;

            begin
               G_Proof_Ins := Global_Id'(Kind => Proof_Ins_Kind,
                                         Name => N);

               G_Ins       := Global_Id'(Kind => Ins_Kind,
                                         Name => N);

               G_Outs      := Global_Id'(Kind => Outs_Kind,
                                         Name => N);

               if Present (Subprogram) then
                  Get_Globals (Subprogram => Subprogram,
                               Scope      => Get_Flow_Scope (Subprogram),
                               Classwide  => False,
                               Proof_Ins  => FS_Proof_Ins,
                               Reads      => FS_Reads,
                               Writes     => FS_Writes);

                  Add_Edges_For_FS (FS_Proof_Ins, G_Proof_Ins);
                  Add_Edges_For_FS (FS_Reads, G_Ins);
                  Add_Edges_For_FS (FS_Writes, G_Outs);
               end if;
            end;
         end loop;

         --  Close graph, but only add edges that are not in the local
         --  graph.
         Global_Graph.Conditional_Close (Edge_Selector'Access);

         -----------------------
         -- Create call graph --
         -----------------------

         --  To detect potentially blocking operations in protected actions
         --  we create a call graph with vertices corresponding to callable
         --  subprograms (i.e. entries, functions and procedures).
         --
         --  All edges originate from subprograms in SPARK, since subprograms
         --  not in SPARK are considered to be potentially blocking anyway
         --  (they are "leaves" of the call graph).
         --
         declare
            Protected_Actions_In_Current_Compilation_Unit : Boolean := False;
            --  Call graphs are needed only if there are protected actions in
            --  the current compilation unit.

            V_Caller, V_Callee : Entity_Name_Graphs.Vertex_Id;

            procedure Find_Vertex
              (E_Name : Entity_Name;
               V      : out Entity_Name_Graphs.Vertex_Id)
              with Post => V /= Entity_Name_Graphs.Null_Vertex;
            --  Find Vertex_Id of subprogram represented by entity
            --  name E_Name in Call_Graph; create such vertex if it
            --  does not already exists.

            -----------------
            -- Find_Vertex --
            -----------------

            procedure Find_Vertex
              (E_Name : Entity_Name;
               V      : out Entity_Name_Graphs.Vertex_Id)
            is
            begin
               V := Call_Graph.Get_Vertex (E_Name);
               if V = Entity_Name_Graphs.Null_Vertex then
                  Call_Graph.Add_Vertex (E_Name, V);
               end if;
            end Find_Vertex;

         begin
            --  Check if there are any entries in the current compilation unit;
            --  if not then we do not need to create a call graph.
            for Subprogram_Info of Subprogram_Info_List loop
               case Subprogram_Info.Kind is
                  when Kind_Entry =>
                     Protected_Actions_In_Current_Compilation_Unit := True;
                     exit;

                  when Kind_Subprogram =>
                     declare
                        E : constant Entity_Id :=
                          Find_Entity (Subprogram_Info.Name);
                     begin
                        if Present (E)
                          and then Convention (E) = Convention_Protected
                        then
                           Protected_Actions_In_Current_Compilation_Unit :=
                             True;
                           exit;
                        end if;
                     end;

                  when others =>
                     null;

               end case;
            end loop;

            if Protected_Actions_In_Current_Compilation_Unit then
               for Subprogram_Info of Subprogram_Info_List loop

                  if Subprogram_Info.Kind in Kind_Subprogram | Kind_Entry
                  then
                     Find_Vertex (Subprogram_Info.Name, V_Caller);
                     declare
                        Calls : constant Name_Sets.Set :=
                          Computed_Calls (Subprogram_Info.Name);
                     begin
                        for Callee of Calls loop
                           Find_Vertex (Callee, V_Callee);
                           Call_Graph.Add_Edge (V_Caller, V_Callee);
                        end loop;
                     end;
                  end if;
               end loop;

               --  Close the call graph
               Call_Graph.Close;
            end if;
         end;
      end Add_All_Edges;

      -------------------------
      -- Create_All_Vertices --
      -------------------------

      procedure Create_All_Vertices is
         use Global_Graphs;
      begin
         --  Create vertices for all global variables
         for N of All_Globals loop
            Global_Graph.Add_Vertex (Global_Id'(Kind => Variable_Kind,
                                                Name => N));
         end loop;

         --  Create Ins, Outs and Proof_Ins vertices for all subprograms
         for N of All_Subprograms loop
            declare
               G_Ins       : constant Global_Id :=
                 Global_Id'(Kind => Ins_Kind,
                            Name => N);

               G_Outs      : constant Global_Id :=
                 Global_Id'(Kind => Outs_Kind,
                            Name => N);

               G_Proof_Ins : constant Global_Id :=
                 Global_Id'(Kind => Proof_Ins_Kind,
                            Name => N);
            begin
               Global_Graph.Add_Vertex (G_Ins);
               Global_Graph.Add_Vertex (G_Outs);
               Global_Graph.Add_Vertex (G_Proof_Ins);

               --  Also add vertex to the tasking-info graphs
               for Kind in Tasking_Info_Kind loop
                  Tasking_Graph (Kind).Add_Vertex (N);
                  --  ??? subprogram vertices can be created when adding edges
               end loop;
            end;
         end loop;

         --  Lastly, create vertices for variables that come from the
         --  Get_Globals function.
         for N of All_Other_Subprograms loop
            declare
               Subprogram   : constant Entity_Id := Find_Entity (N);
               FS_Proof_Ins : Flow_Id_Sets.Set;
               FS_Reads     : Flow_Id_Sets.Set;
               FS_Writes    : Flow_Id_Sets.Set;

               procedure Create_Vertices_For_FS (FS : Flow_Id_Sets.Set);
               --  Creates a vertex for every Flow_Id in FS that
               --  does not already have one.

               ----------------------------
               -- Create_Vertices_For_FS --
               ----------------------------

               procedure Create_Vertices_For_FS (FS : Flow_Id_Sets.Set) is
                  G   : Global_Id;
                  Nam : Entity_Name;
               begin
                  for F of FS loop
                     Nam := (if F.Kind in Direct_Mapping | Record_Field then
                                To_Entity_Name (Get_Direct_Mapping_Id (F))
                             elsif F.Kind = Magic_String then
                                F.Name
                             else
                                raise Program_Error);
                     G   := Global_Id'(Kind => Variable_Kind,
                                       Name => Nam);

                     if Global_Graph.Get_Vertex (G) = Null_Vertex then
                        Global_Graph.Add_Vertex (G);
                     end if;
                  end loop;
               end Create_Vertices_For_FS;

            begin
               if Subprogram /= Empty then
                  Get_Globals (Subprogram => Subprogram,
                               Scope      => Get_Flow_Scope (Subprogram),
                               Classwide  => False,
                               Proof_Ins  => FS_Proof_Ins,
                               Reads      => FS_Reads,
                               Writes     => FS_Writes);

                  Create_Vertices_For_FS (FS_Proof_Ins);
                  Create_Vertices_For_FS (FS_Reads);
                  Create_Vertices_For_FS (FS_Writes);
               end if;
            end;
         end loop;
      end Create_All_Vertices;

      ------------------------
      -- Create_Local_Graph --
      ------------------------

      procedure Create_Local_Graph is
         use Global_Graphs;

         G_Subp       : Global_Id;
         G_Local_Subp : Global_Id;
         G_Local_Var  : Global_Id;

      --  Start of processing for Create_Local_Graph

      begin
         for Info of Subprogram_Info_List loop
            G_Subp := Global_Id'(Kind => Subprogram_Kind,
                                 Name => Info.Name);

            if Local_Graph.Get_Vertex (G_Subp) = Null_Vertex then
               --  Create a vertex for the subprogram if one does not already
               --  exist.
               Local_Graph.Add_Vertex (G_Subp);
            end if;

            --  Create a vertex for every local variable and link it to the
            --  enclosing subprogram.
            for Local_Variable of Info.Local_Variables loop
               G_Local_Var := Global_Id'(Kind => Variable_Kind,
                                         Name => Local_Variable);

               --  Create a vertex for every local variable if one does not
               --  already exist.
               if Local_Graph.Get_Vertex (G_Local_Var) = Null_Vertex then
                  Local_Graph.Add_Vertex (G_Local_Var);
               end if;

               --  Link enclosing subprogram to local variable
               Local_Graph.Add_Edge (G_Subp, G_Local_Var);
            end loop;

            --  Create a vertex for every local subprogram and link it to the
            --  enclosing subprogram.
            for Local_Subprogram of Info.Local_Subprograms loop
               G_Local_Subp := Global_Id'(Kind => Subprogram_Kind,
                                          Name => Local_Subprogram);

               if Local_Graph.Get_Vertex (G_Local_Subp) = Null_Vertex then
                  --  Create a vertex for every local subprogram if one does
                  --  not already exist.
                  Local_Graph.Add_Vertex (G_Local_Subp);
               end if;

               --  Link enclosing subprogram to local subprogram
               Local_Graph.Add_Edge (G_Subp, G_Local_Subp);
            end loop;

            --  Link all local variables to all local subprograms (this
            --  effectively means that they can act as their globals).
            for Local_Variable of Info.Local_Variables loop
               G_Local_Var := Global_Id'(Kind => Variable_Kind,
                                         Name => Local_Variable);

               for Local_Subprogram of Info.Local_Subprograms loop
                  G_Local_Subp := Global_Id'(Kind => Subprogram_Kind,
                                             Name => Local_Subprogram);

                  Local_Graph.Add_Edge (G_Local_Var, G_Local_Subp);
               end loop;
            end loop;
         end loop;

         --  Close graph
         Local_Graph.Close;
      end Create_Local_Graph;

      --------------------------
      -- Create_Tasking_Graph --
      --------------------------

      procedure Create_Tasking_Graph is
         use Entity_Name_Graphs;
      begin
         for Kind in Tasking_Info_Kind loop
            for C in Tasking_Info_Bag (Kind).Iterate loop
               declare
                  Subp : constant Entity_Name   := Key (C);
                  Objs : constant Name_Sets.Set := Element (C);
               begin
                  --  Add vertices for objects
                  for Obj of Objs loop
                     --  Create object vertex if it does not already exist
                     if Tasking_Graph (Kind).Get_Vertex (Obj) = Null_Vertex
                     then
                        Tasking_Graph (Kind).Add_Vertex (Obj);
                     end if;

                     --  Create edge
                     Tasking_Graph (Kind).Add_Edge (Subp, Obj);
                  end loop;
               end;
            end loop;
         end loop;
      end Create_Tasking_Graph;

      --------------------
      -- Edit_Proof_Ins --
      --------------------

      procedure Edit_Proof_Ins is
         use Global_Graphs;

         function Get_Variable_Neighbours
           (Start : Vertex_Id)
            return Vertex_Sets.Set;
         --  Returns a set of all Neighbours of Start that correspond
         --  to variables.

         -----------------------------
         -- Get_Variable_Neighbours --
         -----------------------------

         function Get_Variable_Neighbours
           (Start : Vertex_Id)
            return Vertex_Sets.Set
         is
            VS : Vertex_Sets.Set := Vertex_Sets.Empty_Set;
         begin
            for V of Global_Graph.Get_Collection (Start,
                                                  Out_Neighbours)
            loop
               if Global_Graph.Get_Key (V).Kind = Variable_Kind then
                  VS.Include (V);
               end if;
            end loop;

            return VS;
         end Get_Variable_Neighbours;

      --  Start of processing for Edit_Proof_Ins

      begin
         for Info of Subprogram_Info_List loop
            declare
               G_Ins       : constant Global_Id :=
                 Global_Id'(Kind => Ins_Kind,
                            Name => Info.Name);

               G_Outs      : constant Global_Id :=
                 Global_Id'(Kind => Outs_Kind,
                            Name => Info.Name);

               G_Proof_Ins : constant Global_Id :=
                 Global_Id'(Kind => Proof_Ins_Kind,
                            Name => Info.Name);

               V_Ins       : constant Vertex_Id :=
                 Global_Graph.Get_Vertex (G_Ins);

               V_Outs      : constant Vertex_Id :=
                 Global_Graph.Get_Vertex (G_Outs);

               V_Proof_Ins : constant Vertex_Id :=
                 Global_Graph.Get_Vertex (G_Proof_Ins);

               Inputs      : constant Vertex_Sets.Set :=
                 Get_Variable_Neighbours (V_Ins);

               Outputs     : constant Vertex_Sets.Set :=
                 Get_Variable_Neighbours (V_Outs);

               Proof_Ins   : constant Vertex_Sets.Set :=
                 Get_Variable_Neighbours (V_Proof_Ins);
            begin
               for V of Proof_Ins loop
                  if Inputs.Contains (V)
                    or else Outputs.Contains (V)
                  then
                     if not Global_Graph.Edge_Exists (V_Ins, V) then
                        Global_Graph.Add_Edge (V_Ins, V);
                     end if;

                     Global_Graph.Remove_Edge (V_Proof_Ins, V);
                  end if;
               end loop;
            end;
         end loop;
      end Edit_Proof_Ins;

      ----------------------------------
      -- Generate_Initializes_Aspects --
      ----------------------------------

      procedure Generate_Initializes_Aspects is
      begin
         for P of Package_Info_List loop
            declare
               II        : Initializes_Info;
               --  The new name dependency map for package P

               LHS       : Name_Sets.Set    := Name_Sets.Empty_Set;
               LHS_Proof : Name_Sets.Set    := Name_Sets.Empty_Set;
               --  LHS and LHS_Proof combined will represent the left hand side
               --  of the generated initializes aspect.

               RHS       : Name_Sets.Set    := Name_Sets.Empty_Set;
               RHS_Proof : Name_Sets.Set    := Name_Sets.Empty_Set;
               --  RHS and RHS_Proof combined will represent the left hand side
               --  of the generated initializes aspect.

               LV        : Name_Sets.Set    := Name_Sets.Empty_Set;
               LV_Proof  : Name_Sets.Set    := Name_Sets.Empty_Set;
               --  Flow id sets of local variables/states and local proof
               --  variables/states.

               ODC       : Name_Sets.Set    := Name_Sets.Empty_Set;
               --  Outputs of Definite Calls

               procedure Add_To_Proof_Or_Normal_Set
                 (EN         : Entity_Name;
                  Proof_Set  : in out Name_Sets.Set;
                  Normal_Set : in out Name_Sets.Set);
               --  Adds EN to either Proof_Set or Normal_Set depending on
               --  whether it is a ghost entity or not.

               --------------------------------
               -- Add_To_Proof_Or_Normal_Set --
               --------------------------------

               procedure Add_To_Proof_Or_Normal_Set
                 (EN         : Entity_Name;
                  Proof_Set  : in out Name_Sets.Set;
                  Normal_Set : in out Name_Sets.Set)
               is
                  E : constant Entity_Id := Find_Entity (EN);
               begin
                  if Present (E)
                    and then Is_Ghost_Entity (E)
                  then
                     Proof_Set.Insert (EN);
                  else
                     Normal_Set.Insert (EN);
                  end if;
               end Add_To_Proof_Or_Normal_Set;

            begin
               --  Add inputs to the RHS set
               RHS.Union (P.Inputs);

               --  Add proof inputs to the RHS_Proof set
               RHS_Proof.Union (P.Inputs_Proof);

               --  Add local variables to either LV_Proof or LV depending on
               --  whether they are ghosts or not.
               for Local_Variable of P.Local_Variables loop
                  Add_To_Proof_Or_Normal_Set (Local_Variable,
                                              LV_Proof,
                                              LV);

                  --  Add local state abstractions with null refinements to the
                  --  list of local definite writes since they are trivially
                  --  initialized.
                  if State_Comp_Map.Contains (Local_Variable)
                    and then State_Comp_Map.Element (Local_Variable) =
                               Name_Sets.Empty_Set
                  then
                     Add_To_Proof_Or_Normal_Set (Local_Variable,
                                                 LHS_Proof,
                                                 LHS);
                  end if;
               end loop;

               --  Add definite local writes to either LHS_Proof or LHS
               --  depending on whether they are ghosts or not.
               for Local_Definite_Write of P.Local_Definite_Writes loop
                  Add_To_Proof_Or_Normal_Set (Local_Definite_Write,
                                              LHS_Proof,
                                              LHS);
               end loop;

               --  Add the intersection of pure outputs (outputs that are not
               --  also read) of definite calls and local variables to
               --  LHS. Additionally, add Reads and Proof_Reads of definite
               --  calls to RHS and RHS_Proof respectively.
               for Definite_Call of P.Definite_Calls loop
                  declare
                     Proof_Reads : Name_Sets.Set;
                     Reads       : Name_Sets.Set;
                     Writes      : Name_Sets.Set;
                  begin
                     if GG_Exists_Cache.Contains (Definite_Call) then
                        GG_Get_MR_Globals (EN          => Definite_Call,
                                           Proof_Reads => Proof_Reads,
                                           Reads       => Reads,
                                           Writes      => Writes);

                        RHS_Proof.Union (Proof_Reads);
                        RHS.Union (Reads);
                        ODC.Union (Writes - Reads);
                     end if;
                  end;
               end loop;
               LHS.Union (Name_Sets.Intersection (LV, ODC));

               --  Add Reads and Writes of conditional calls to the RHS set
               --  and their Proof_Reads to the RHS_Proof set.
               for Conditional_Call of P.Conditional_Calls loop
                  declare
                     Proof_Reads : Name_Sets.Set;
                     Reads       : Name_Sets.Set;
                     Writes      : Name_Sets.Set;
                  begin
                     if GG_Exists_Cache.Contains (Conditional_Call) then
                        GG_Get_MR_Globals (EN          => Conditional_Call,
                                           Proof_Reads => Proof_Reads,
                                           Reads       => Reads,
                                           Writes      => Writes);

                        RHS_Proof.Union (Proof_Reads);
                        RHS.Union (Reads);
                        RHS.Union (Writes);
                     end if;
                  end;
               end loop;

               --  Populate II
               II.LHS       := LHS;
               II.LHS_Proof := LHS_Proof;
               II.RHS       := RHS;
               II.RHS_Proof := RHS_Proof;

               --  Add LHS and LHS_Proof to the All_Initialized_Names set
               All_Initialized_Names.Union (II.LHS);
               All_Initialized_Names.Union (II.LHS_Proof);

               --  Add state abstractions to the All_Initialized_Names set when
               --  all constituents are initialized and remove constituents of
               --  state abstractions that are not fully initialized.
               declare
                  All_LHS   : constant Name_Sets.Set := LHS or LHS_Proof;
                  State     : Entity_Name;
                  To_Remove : Name_Sets.Set := Name_Sets.Empty_Set;
               begin
                  for Var of All_LHS loop
                     State := GG_Enclosing_State (Var);

                     if State /= Null_Entity_Name then
                        if (for all Const of GG_Get_Constituents (State)
                              => All_LHS.Contains (Const))
                        then
                           --  All constituents are initialized so we add the
                           --  entire abstract state.
                           All_Initialized_Names.Include (State);
                        else
                           --  At least one constituent is not initialized so
                           --  there is no point in considering the current
                           --  constituent alone as being initialized.
                           To_Remove.Insert (Var);
                        end if;
                     end if;
                  end loop;

                  --  Remove constituents whose eclosing state abstraction is
                  --  not fully initialized.
                  All_Initialized_Names := All_Initialized_Names - To_Remove;
                  II.LHS                := II.LHS - To_Remove;
                  II.LHS_Proof          := II.LHS_Proof - To_Remove;
               end;

               --  Insert II into Initializes_Aspects_Map
               Initializes_Aspects_Map.Insert (P.Name, II);

            end;
         end loop;

         if Debug_Print_Generated_Initializes then
            Print_Generated_Initializes_Aspects;
         end if;
      end Generate_Initializes_Aspects;

      ---------------------------
      -- Load_GG_Info_From_ALI --
      ---------------------------

      procedure Load_GG_Info_From_ALI (ALI_File_Name : File_Name_Type) is
         ALI_File_Name_Str : constant String :=
           Name_String (Name_Id (Full_Lib_File_Name (ALI_File_Name)));

         Sanitized_Name : constant Unbounded_String :=
           Trim (Source => To_Unbounded_String (ALI_File_Name_Str),
                 Left   => Null_Set,
                 Right  => To_Set (Character'Val (0)));

         procedure Issue_Corrupted_File_Error (Msg : String)
         with No_Return;
         --  Issues an error about the ALI file being corrupted and
         --  suggests the usage of "gnatprove --clean".

         --------------------------------
         -- Issue_Corrupted_File_Error --
         --------------------------------

         procedure Issue_Corrupted_File_Error (Msg : String) is
         begin
            Abort_With_Message
              ("Corrupted ali file detected (" &
                 To_String (Sanitized_Name) & "): " &
                 Msg &
                 ". Call gnatprove with ""--clean"".");
         end Issue_Corrupted_File_Error;

         ALI_File  : Ada.Text_IO.File_Type;
         Line      : Unbounded_String;

         Found_End : Boolean := False;
         --  This will be set to True once we find the end marker.
      begin
         Open (ALI_File, In_File, ALI_File_Name_Str);

         --  Skip to the GG section (this should be the very last section).
         loop
            if End_Of_File (ALI_File) then
               Close (ALI_File);
               return;
            end if;

            Get_Line (ALI_File, Line);
            exit when Length (Line) >= 3 and then Slice (Line, 1, 3) = "GG ";
         end loop;

         --  We have reached the "GG" section of the ALI file
         while Length (Line) >= 5 and then Slice (Line, 1, 3) = "GG " loop
            --  Parse the given record.
            declare
               A : Archive (Serialisation.Input) :=
                 From_String (Unbounded_Slice (Line, 4, Length (Line)));
               V : ALI_Entry := (Kind => EK_Error);
            begin
               Serialize (A, V);
               case V.Kind is
                  when EK_Error =>
                     Issue_Corrupted_File_Error ("parse error");

                  when EK_End_Marker =>
                     Found_End := True;
                     exit;

                  when EK_State_Map =>
                     State_Comp_Map.Include (V.The_State,
                                             V.The_Constituents);

                  when EK_Volatiles =>
                     Async_Writers_Vars.Union (V.All_Async_Writers);
                     All_Volatile_Vars.Union (V.All_Async_Writers);

                     Async_Readers_Vars.Union (V.All_Async_Readers);
                     All_Volatile_Vars.Union (V.All_Async_Readers);

                     Effective_Reads_Vars.Union (V.All_Effective_Reads);
                     All_Volatile_Vars.Union (V.All_Effective_Reads);

                     Effective_Writes_Vars.Union (V.All_Effective_Writes);
                     All_Volatile_Vars.Union (V.All_Effective_Writes);

                  when EK_Globals =>
                     All_Globals.Union (V.The_Global_Info.Inputs_Proof);
                     All_Globals.Union (V.The_Global_Info.Inputs);
                     All_Globals.Union (V.The_Global_Info.Outputs);

                     All_Subprograms.Union (V.The_Global_Info.Proof_Calls);
                     All_Subprograms.Union (V.The_Global_Info.Definite_Calls);
                     All_Subprograms.Union
                       (V.The_Global_Info.Conditional_Calls);

                     All_Globals.Union (V.The_Global_Info.Local_Variables);
                     All_Subprograms.Union
                       (V.The_Global_Info.Local_Subprograms);
                     All_Globals.Union
                       (V.The_Global_Info.Local_Definite_Writes);

                     case V.The_Global_Info.Kind is
                        when Kind_Subprogram | Kind_Entry | Kind_Task =>
                           GG_Subprograms.Include (V.The_Global_Info.Name);
                           All_Subprograms.Include (V.The_Global_Info.Name);

                           Subprogram_Info_List.Append (V.The_Global_Info);

                        when Kind_Package | Kind_Package_Body =>
                           Package_Info_List.Append (V.The_Global_Info);
                     end case;

                     GG_Exists_Cache.Insert (V.The_Global_Info.Name);

                  when EK_Tasking_Instance_Count =>
                     if Task_Instances.Contains (V.The_Type) then
                        Task_Instances.Include (V.The_Type, Many);
                     else
                        Task_Instances.Include (V.The_Type, V.The_Count);
                     end if;

                  when EK_Tasking_Info =>
                     for Kind in Tasking_Info_Kind loop
                        if not V.The_Tasking_Info (Kind).Is_Empty then
                           Tasking_Info_Bag (Kind).Insert
                             (V.The_Entity,
                              V.The_Tasking_Info (Kind));
                        end if;
                     end loop;

                  when EK_Tasking_Nonblocking =>
                     Nonblocking_Subprograms_Set.Union
                       (V.The_Nonblocking_Subprograms);
               end case;
            end;

            exit when End_Of_File (ALI_File);

            --  Proceed to the next line.
            Get_Line (ALI_File, Line);
         end loop;

         if not Found_End then
            --  If we have not found the end marker by now, the file is
            --  broken...
            Issue_Corrupted_File_Error ("missing end marker");
         end if;

         Close (ALI_File);
      end Load_GG_Info_From_ALI;

      ----------------------------
      -- Print_Tasking_Info_Bag --
      ----------------------------

      procedure Print_Tasking_Info_Bag is
      begin
         if not Debug_Print_Tasking_Info then
            return;
         end if;

         for Kind in Tasking_Info_Kind loop
            Write_Line ("Tasking: " & Kind'Img);
            Indent;
            if not Tasking_Info_Bag (Kind).Is_Empty then
               for C in Tasking_Info_Bag (Kind).Iterate loop
                  declare
                     Subp : constant Entity_Name   := Key (C);
                     Objs : constant Name_Sets.Set := Element (C);
                  begin
                     if not Objs.Is_Empty then
                        Write_Line (To_String (Subp) & ":");
                        Indent;
                        for Obj of Objs loop
                           Write_Line (To_String (Obj));
                        end loop;
                        Outdent;
                     end if;
                  end;
               end loop;
            end if;
            Outdent;
         end loop;
      end Print_Tasking_Info_Bag;

      ---------------------------
      -- Process_Tasking_Graph --
      ---------------------------

      procedure Process_Tasking_Graph is
         use Entity_Name_Graphs;
      begin
         for Kind in Tasking_Info_Kind loop
            --  Do the transitive closure
            Tasking_Graph (Kind).Close;

            --  Clear the bag
            Tasking_Info_Bag (Kind).Clear;

            --  Collect information for each subprogram
            for S of All_Subprograms loop
               declare
                  S_Vertex : constant Vertex_Id :=
                    Tasking_Graph (Kind).Get_Vertex (S);
                  Objs : Name_Sets.Set := Name_Sets.Empty_Set;
               begin
                  --  Collect out-neighbours of the subprogram vertex
                  for Obj_Key of Tasking_Graph (Kind).Get_Collection
                    (S_Vertex, Out_Neighbours)
                  loop
                     Objs.Insert (Tasking_Graph (Kind).Get_Key (Obj_Key));
                  end loop;

                  --  Remove called subprograms
                  Objs := Objs - All_Subprograms;

                  --  Store the non-empty results
                  if not Objs.Is_Empty then
                     Tasking_Info_Bag (Kind).Insert (S, Objs);
                  end if;
               end;
            end loop;
         end loop;
      end Process_Tasking_Graph;

      ---------------------------------------------
      -- Remove_Constants_Without_Variable_Input --
      ---------------------------------------------

      procedure Remove_Constants_Without_Variable_Input
      is
         use Global_Graphs;

         All_Constants : Name_Sets.Set := Name_Sets.Empty_Set;
      begin
         --  Gather up all constants without variable input
         for Glob of All_Globals loop
            declare
               Const : constant Entity_Id := Find_Entity (Glob);
            begin
               if Const /= Empty
                 and then Ekind (Const) = E_Constant
                 and then not Has_Variable_Input (Direct_Mapping_Id (Const))
               then
                  All_Constants.Include (Glob);
               end if;
            end;
         end loop;

         --  Remove all edges going in and out of a constant without
         --  variable input.
         for Const of All_Constants loop
            declare
               Const_G_Id : constant Global_Id :=
                 Global_Id'(Kind => Variable_Kind,
                            Name => Const);

               Const_V    : constant Vertex_Id :=
                 Global_Graph.Get_Vertex (Const_G_Id);
            begin
               Global_Graph.Clear_Vertex (Const_V);
            end;
         end loop;
      end Remove_Constants_Without_Variable_Input;

   --  Start of processing for GG_Read

   begin
      Current_Mode := GG_Read_Mode;

      if Debug_GG_Read_Timing then
         Init_Time ("gg_read");
      end if;

      --  Initialize volatile info
      All_Volatile_Vars     := Name_Sets.Empty_Set;
      Async_Writers_Vars    := Name_Sets.Empty_Set;
      Async_Readers_Vars    := Name_Sets.Empty_Set;
      Effective_Reads_Vars  := Name_Sets.Empty_Set;
      Effective_Writes_Vars := Name_Sets.Empty_Set;

      --  Go through all ALI files and populate the Subprogram_Info_List.
      declare
         Read_Files : Unbounded_String_Sets.Set;
         Nam        : Unbounded_String;
      begin
         Read_Files := Unbounded_String_Sets.Empty_Set;
         for Index in ALIs.First .. ALIs.Last loop
            --  ??? The ALI table seems to incldue some entries twice, but
            --  that is because some of them are null-terminated. See
            --  O714-006; this is the workaround for now.
            Nam := To_Unbounded_String
              (Name_String (Name_Id (Full_Lib_File_Name
                                       (ALIs.Table (Index).Afile))));
            Nam := Trim (Source => Nam,
                         Left   => Null_Set,
                         Right  => To_Set (Character'Val (0)));
            if not Read_Files.Contains (Nam) then
               Read_Files.Insert (Nam);
               Load_GG_Info_From_ALI (ALIs.Table (Index).Afile);
            end if;
         end loop;
      end;

      if Debug_GG_Read_Timing then
         Note_Time ("gg_read - ALI files read");
      end if;

      if Debug_Print_Info_Sets_Read then
         --  Print all GG related info gathered from the ALI files.
         for Info of Subprogram_Info_List loop
            Write_Eol;
            Print_Global_Phase_1_Info (Info);
         end loop;

         for C in State_Comp_Map.Iterate loop
            declare
               State : constant Entity_Name := Key (C);
               Constituents : constant Name_Sets.Set := Element (C);
            begin
               Write_Eol;
               Write_Line ("Abstract state " & To_String (State));

               Write_Line ("Constituents     :");
               for Name of Constituents loop
                  Write_Line ("   " & To_String (Name));
               end loop;
            end;
         end loop;

         --  Print all volatile info
         Write_Eol;

         Write_Line ("Async_Writers    :");
         for Name of Async_Writers_Vars loop
            Write_Line ("   " & To_String (Name));
         end loop;

         Write_Line ("Async_Readers    :");
         for Name of Async_Readers_Vars loop
            Write_Line ("   " & To_String (Name));
         end loop;

         Write_Line ("Effective_Reads  :");
         for Name of Effective_Reads_Vars loop
            Write_Line ("   " & To_String (Name));
         end loop;

         Write_Line ("Effective_Writes :");
         for Name of Effective_Writes_Vars loop
            Write_Line ("   " & To_String (Name));
         end loop;
      end if;

      --  Populate the All_Other_Subprograms set
      All_Other_Subprograms := All_Subprograms - GG_Subprograms;

      --  Initialize Local_Graph and Global_Graph
      Local_Graph  := Global_Graphs.Create;
      Global_Graph := Global_Graphs.Create;

      --  Create the Local_Graph
      Create_Local_Graph;
      if Debug_GG_Read_Timing then
         Note_Time ("gg_read - local graph done");
      end if;

      --  Create all vertices of the Global_Graph
      Create_All_Vertices;
      if Debug_GG_Read_Timing then
         Note_Time ("gg_read - vertices added");
      end if;

      --  Create graph with tasking-related information
      Create_Tasking_Graph;

      --  Add all edges in the Global_Graph and Tasking_Graph
      Add_All_Edges;
      if Debug_GG_Read_Timing then
         Note_Time ("gg_read - edges added");
      end if;

      --  Edit Proof_Ins
      Edit_Proof_Ins;
      if Debug_GG_Read_Timing then
         Note_Time ("gg_read - proof ins");
      end if;

      --  Put tasking-related information back to the bag
      Process_Tasking_Graph;
      Print_Tasking_Info_Bag;

      --  Now that the Globals Graph has been generated we set
      --  GG_Generated to True. Notice that we set GG_Generated to
      --  True before we remove edges leading to constants without
      --  variable input. The reasoning behind this is to use the
      --  generated globals instead of the computed globals when we
      --  call Get_Globals from within Has_Variable_Input.
      GG_Generated := True;

      --  Remove edges leading to constants which do not have variable
      --  input.
      Remove_Constants_Without_Variable_Input;
      if Debug_GG_Read_Timing then
         Note_Time ("gg_read - removed nonvariable constants");
      end if;

      if Debug_Print_Global_Graph then
         declare
            Common_Prefix : constant String :=
              Spec_File_Name_Without_Suffix
                (Enclosing_Comp_Unit_Node (GNAT_Root));

            LG_Filename   : constant String :=
              Common_Prefix & "_locals_graph";

            GG_Filename   : constant String :=
              Common_Prefix & "_globals_graph";
         begin
            Print_Global_Graph (Filename => LG_Filename,
                                G        => Local_Graph);

            Print_Global_Graph (Filename => GG_Filename,
                                G        => Global_Graph);
         end;
      end if;

      --  To speed up queries on constituents of state, we fill in a helper
      --  structure.
      Comp_State_Map := Name_Maps.Empty_Map;
      for C in State_Comp_Map.Iterate loop
         for Comp of Element (C) loop
            Comp_State_Map.Insert (Comp, Key (C));
         end loop;
      end loop;

      --  Now that the globals are generated, we use them to also generate the
      --  initializes aspects.
      Generate_Initializes_Aspects;

      if Debug_GG_Read_Timing then
         Final_Time ("gg_read");
      end if;

   end GG_Read;

   --------------
   -- GG_Exist --
   --------------

   function GG_Exist (E : Entity_Id) return Boolean is
      Name : constant Entity_Name := To_Entity_Name (E);
   begin
      return GG_Exists_Cache.Contains (Name);
   end GG_Exist;

   -----------------------
   -- GG_Has_Refinement --
   -----------------------

   function GG_Has_Refinement (EN : Entity_Name) return Boolean is
   begin
      return State_Comp_Map.Contains (EN);
   end GG_Has_Refinement;

   -----------------------
   -- GG_Is_Constituent --
   -----------------------

   function GG_Is_Constituent (EN : Entity_Name) return Boolean is
   begin
      return Comp_State_Map.Contains (EN);
   end GG_Is_Constituent;

   -------------------------
   -- GG_Get_Constituents --
   -------------------------

   function GG_Get_Constituents (EN : Entity_Name) return Name_Sets.Set is
   begin
      return (if State_Comp_Map.Contains (EN)
              then State_Comp_Map.Element (EN)
              else Name_Sets.Empty_Set);
   end GG_Get_Constituents;

   ------------------------
   -- GG_Enclosing_State --
   ------------------------

   function GG_Enclosing_State (EN : Entity_Name) return Entity_Name is
   begin
      return (if Comp_State_Map.Contains (EN)
              then Comp_State_Map.Element (EN)
              else Null_Entity_Name);
   end GG_Enclosing_State;

   ---------------------
   -- GG_Fully_Refine --
   ---------------------

   function GG_Fully_Refine (EN : Entity_Name) return Name_Sets.Set is
      NS       : Name_Sets.Set;
      Tmp_Name : Entity_Name;
   begin
      NS := GG_Get_Constituents (EN);

      while (for some S of NS => GG_Has_Refinement (S)) loop
         Tmp_Name := Null_Entity_Name;
         for S of NS loop
            if GG_Has_Refinement (S) then
               Tmp_Name := S;
               exit;
            end if;
         end loop;

         if Tmp_Name /= Null_Entity_Name then
            NS.Union (GG_Get_Constituents (Tmp_Name));
            NS.Exclude (Tmp_Name);
         end if;
      end loop;

      return NS;
   end GG_Fully_Refine;

   -----------------------
   -- GG_Get_MR_Globals --
   -----------------------

   procedure GG_Get_MR_Globals (EN          : Entity_Name;
                                Proof_Reads : out Name_Sets.Set;
                                Reads       : out Name_Sets.Set;
                                Writes      : out Name_Sets.Set)
   is
      use Global_Graphs;

      G_Proof_Ins     : constant Global_Id :=
        Global_Id'(Kind => Proof_Ins_Kind,
                   Name => EN);
      G_Ins           : constant Global_Id :=
        Global_Id'(Kind => Ins_Kind,
                   Name => EN);
      G_Outs          : constant Global_Id :=
        Global_Id'(Kind => Outs_Kind,
                   Name => EN);
      --  The above 3 Global_Ids correspond to the subprogram's Ins,
      --  Outs and Proof_Ins.

      V_Proof_Ins     : constant Vertex_Id :=
        Global_Graph.Get_Vertex (G_Proof_Ins);
      V_Ins           : constant Vertex_Id :=
        Global_Graph.Get_Vertex (G_Ins);
      V_Outs          : constant Vertex_Id :=
        Global_Graph.Get_Vertex (G_Outs);
      --  The above 3 Vertex_Ids correspond to the subprogram's Ins,
      --  Outs and Proof_Ins.

      function Calculate_MR (Start : Vertex_Id) return Name_Sets.Set;
      --  Returns a set of all vertices that can be reached from Start and are
      --  of the Variable_Kind.

      ------------------
      -- Calculate_MR --
      ------------------

      function Calculate_MR (Start : Vertex_Id) return Name_Sets.Set is
         NS : Name_Sets.Set := Name_Sets.Empty_Set;
         G  : Global_Id;
      begin
         for V of Global_Graph.Get_Collection (Start, Out_Neighbours) loop
            G := Global_Graph.Get_Key (V);

            if G.Kind = Variable_Kind then
               NS.Include (G.Name);
            end if;
         end loop;

         return NS;
      end Calculate_MR;

   begin
      --  Calculate MR_Proof_Reads, MR_Reads and MR_Writes
      Proof_Reads := Calculate_MR (V_Proof_Ins);
      Reads       := Calculate_MR (V_Ins);
      Writes      := Calculate_MR (V_Outs);
   end GG_Get_MR_Globals;

   --------------------
   -- GG_Get_Globals --
   --------------------

   procedure GG_Get_Globals (E           : Entity_Id;
                             S           : Flow_Scope;
                             Proof_Reads : out Flow_Id_Sets.Set;
                             Reads       : out Flow_Id_Sets.Set;
                             Writes      : out Flow_Id_Sets.Set)
   is
      MR_Proof_Reads  : Name_Sets.Set := Name_Sets.Empty_Set;
      MR_Reads        : Name_Sets.Set := Name_Sets.Empty_Set;
      MR_Writes       : Name_Sets.Set := Name_Sets.Empty_Set;
      --  The above 3 sets will contain the most refined views of their
      --  respective globals.

      Temp_NS         : Name_Sets.Set;
      Unused          : Flow_Id_Sets.Set;

   begin
      --  Initialize the Proof_Reads, Reads and Writes sets
      Proof_Reads := Flow_Id_Sets.Empty_Set;
      Reads       := Flow_Id_Sets.Empty_Set;
      Writes      := Flow_Id_Sets.Empty_Set;

      --  Call GG_Get_MR_Globals to calculate MR_Proof_Reads, MR_Reads and
      --  MR_Writes.
      GG_Get_MR_Globals (To_Entity_Name (E),
                         MR_Proof_Reads,
                         MR_Reads,
                         MR_Writes);

      --  Up project variables based on scope S and give Flow_Ids
      --  their correct views.
      Up_Project (Most_Refined => MR_Proof_Reads,
                  Final_View   => Temp_NS,
                  Scope        => S,
                  Reads        => Unused);
      Proof_Reads.Union (To_Flow_Id_Set (Temp_NS, In_View, S));

      Up_Project (Most_Refined => MR_Reads,
                  Final_View   => Temp_NS,
                  Scope        => S,
                  Reads        => Unused);
      Reads.Union (To_Flow_Id_Set (Temp_NS, In_View, S));

      Up_Project (Most_Refined      => MR_Writes,
                  Final_View        => Temp_NS,
                  Scope             => S,
                  Reads             => Reads,
                  Processing_Writes => True);
      Writes.Union (To_Flow_Id_Set (Temp_NS, Out_View, S));
   end GG_Get_Globals;

   -----------------------------------
   -- GG_Get_All_State_Abstractions --
   -----------------------------------

   function GG_Get_All_State_Abstractions return Name_Sets.Set is
      Tmp : Name_Sets.Set := Name_Sets.Empty_Set;
   begin
      for C in State_Comp_Map.Iterate loop
         Tmp.Insert (Key (C));
      end loop;

      return Tmp;
   end GG_Get_All_State_Abstractions;

   ------------------------
   -- GG_Get_Initializes --
   ------------------------

   function GG_Get_Initializes
     (EN : Entity_Name;
      S  : Flow_Scope)
      return Dependency_Maps.Map
   is
   begin
      --  If we have no info for this package then we cannot have possibly
      --  generated an initializes package for it.
      if not GG_Exists_Cache.Contains (EN) then
         return Dependency_Maps.Empty_Map;
      end if;

      --  Retrieve the relevant Name_Dependency_Map, up project it to S and
      --  then convert it into a Dependency_Map.
      declare
         Pkg          : constant Entity_Id        := Find_Entity (EN);
         LHS_Scope    : Flow_Scope;

         DM           : Dependency_Maps.Map;
         II           : constant Initializes_Info :=
           Initializes_Aspects_Map.Element (EN);

         All_LHS_UP   : Name_Sets.Set;
         LHS_UP       : Name_Sets.Set;
         LHS_Proof_UP : Name_Sets.Set;
         RHS_UP       : Name_Sets.Set;
         RHS_Proof_UP : Name_Sets.Set;

         To_Remove    : Flow_Id_Sets.Set          := Flow_Id_Sets.Empty_Set;
         --  This set will hold the names of non fully initialized
         --  states. These will have to be removed from the left hand side
         --  sets.

         FS_LHS       : Flow_Id_Sets.Set;
         FS_LHS_Proof : Flow_Id_Sets.Set;
         FS_RHS       : Flow_Id_Sets.Set;
         FS_RHS_Proof : Flow_Id_Sets.Set;
         --  These will hold the final flow sets that will be used to populate
         --  the dependency map.

         Unused       : Flow_Id_Sets.Set;
      begin

         if Present (Pkg) then
            LHS_Scope := Flow_Scope'(Ent     => Pkg,
                                     Section => Spec_Part);
         else
            LHS_Scope := S;
         end if;

         --  Up project left hand side
         Up_Project (Most_Refined      => II.LHS or II.LHS_Proof,
                     Final_View        => All_LHS_UP,
                     Scope             => LHS_Scope,
                     Reads             => To_Remove,
                     Processing_Writes => True);

         Up_Project (Most_Refined => II.LHS,
                     Final_View   => LHS_UP,
                     Scope        => LHS_Scope,
                     Reads        => Unused);

         Up_Project (Most_Refined => II.LHS_Proof,
                     Final_View   => LHS_Proof_UP,
                     Scope        => LHS_Scope,
                     Reads        => Unused);

         --  Up project right hand side
         Up_Project (Most_Refined => II.RHS,
                     Final_View   => RHS_UP,
                     Scope        => S,
                     Reads        => Unused);

         Up_Project (Most_Refined => II.RHS_Proof,
                     Final_View   => RHS_Proof_UP,
                     Scope        => S,
                     Reads        => Unused);

         --  Populate and return DM
         FS_LHS       := To_Flow_Id_Set (LHS_UP);
         FS_LHS_Proof := To_Flow_Id_Set (LHS_Proof_UP);
         FS_RHS       := To_Flow_Id_Set (RHS_UP);
         FS_RHS_Proof := To_Flow_Id_Set (RHS_Proof_UP);

         --  Remove state abstractions that are only partially initialized from
         --  the left hand side.
         FS_LHS       := FS_LHS - To_Remove;
         FS_LHS_Proof := FS_LHS_Proof - To_Remove;

         --  Add regular variables
         for F of FS_LHS loop
            DM.Insert (F, FS_RHS);
         end loop;
         --  Add proof variables
         for F of FS_LHS_Proof loop
            DM.Insert (F, FS_RHS_Proof);
         end loop;

         return DM;
      end;
   end GG_Get_Initializes;

   --------------------------------------
   -- GG_Is_Initialized_At_Elaboration --
   --------------------------------------

   function GG_Is_Initialized_At_Elaboration
     (EN : Entity_Name)
      return Boolean
   is
   begin
      return All_Initialized_Names.Contains (EN);
   end GG_Is_Initialized_At_Elaboration;

   --------------------
   -- GG_Is_Volatile --
   --------------------

   function GG_Is_Volatile (EN : Entity_Name) return Boolean is
   begin
      return All_Volatile_Vars.Contains (EN);
   end GG_Is_Volatile;

   --------------------------
   -- GG_Has_Async_Writers --
   --------------------------

   function GG_Has_Async_Writers (EN : Entity_Name) return Boolean is
   begin
      return Async_Writers_Vars.Contains (EN);
   end GG_Has_Async_Writers;

   --------------------------
   -- GG_Has_Async_Readers --
   --------------------------

   function GG_Has_Async_Readers (EN : Entity_Name) return Boolean is
   begin
      return Async_Readers_Vars.Contains (EN);
   end GG_Has_Async_Readers;

   ----------------------------
   -- GG_Has_Effective_Reads --
   ----------------------------

   function GG_Has_Effective_Reads (EN : Entity_Name) return Boolean is
   begin
      return Effective_Reads_Vars.Contains (EN);
   end GG_Has_Effective_Reads;

   -----------------------------
   -- GG_Has_Effective_Writes --
   -----------------------------

   function GG_Has_Effective_Writes (EN : Entity_Name) return Boolean is
   begin
      return Effective_Writes_Vars.Contains (EN);
   end GG_Has_Effective_Writes;

   -----------------------------
   -- Is_Potentially_Blocking --
   -----------------------------

   function Is_Potentially_Blocking (E : Entity_Id) return Boolean is
      EN : constant Entity_Name := To_Entity_Name (E);
      --  Entity name

      Protected_Type_E : constant Entity_Id := Scope (E);
      --  Entity of the enclosing protected type

      function Calls_Potentially_Blocking_Subprogram return Boolean;
      pragma Unreferenced (Calls_Potentially_Blocking_Subprogram);
      --  Check for calls to potentially blocking subprograms of a given Kind

      -------------------------------------------
      -- Calls_Potentially_Blocking_Subprogram --
      -------------------------------------------

      function Calls_Potentially_Blocking_Subprogram return Boolean
      is
         use Entity_Name_Graphs;

         Caller : constant Vertex_Id := Call_Graph.Get_Vertex (EN);
         --  Vertex that represents the analysed subprogram

         Callee : Entity_Name;

         function Calls_Same_Target_Type (S : Entity_Name) return Boolean;
         --  Check if subprogram S calls the enclosing protected type of E

         function Is_Predefined (Subprogram : String) return Boolean;
         --  Check if Subprogram is in a unit predefined by the Ada RM

         ----------------------------
         -- Calls_Same_Target_Type --
         ----------------------------

         function Calls_Same_Target_Type (S : Entity_Name) return Boolean is
            Subp_V : constant Vertex_Id := Call_Graph.Get_Vertex (S);
            --  Vertex that represents subprogram S

            Callee : Entity_Name;
            --  Vertex that represent subprogram called by S
         begin
            --  Iterate over subprograms called by subprogram S
            for V of Call_Graph.Get_Collection (Subp_V, Out_Neighbours) loop

               Callee := Call_Graph.Get_Key (V);

               declare
                  Callee_E : constant Entity_Id := Find_Entity (Callee);
               begin
                  if Present (Callee_E)
                    and then Scope (Callee_E) = Protected_Type_E
                  then
                     return True;
                  end if;
               end;

            end loop;

            return False;
         end Calls_Same_Target_Type;

         -------------------
         -- Is_Predefined --
         -------------------

         function Is_Predefined (Subprogram : String) return Boolean is
         begin
            return Match (Predefined, Subprogram);
         end Is_Predefined;

      --  Start of processing for Calls_Potentially_Blocking_Subprogram

      begin

         for V of Call_Graph.Get_Collection (Caller, Out_Neighbours) loop

            Callee := Call_Graph.Get_Key (V);

            declare
               Callee_E : constant Entity_Id := Find_Entity (Callee);
               --  Entities from other compilation units have empty id
            begin
               if Is_Predefined (To_String (Callee)) then
                  --  All user-defined callers of predefined potentially
                  --  blocking subprograms have been already marked as
                  --  potentially blocking, so here we can safely assume
                  --  that any call to predefined subprogram is nonblocking.
                  null;
               else
                  if not Nonblocking_Subprograms_Set.Contains (Callee) then
                     return True;
                  end if;
               end if;

               --  Check for external calls to a protected subprogram with
               --  the same target type as that of the protected action.
               if Callee_E = Empty
                 or else not Scope_Within_Or_Same (Scope (Callee_E),
                                                   Protected_Type_E)
               then
                  if Calls_Same_Target_Type (Callee) then
                     return True;
                  end if;
               end if;

               --  ??? remote subprograms
            end;

         end loop;

         return False;

      end Calls_Potentially_Blocking_Subprogram;

   --  Start of processing for Is_Potentially_Blocking

   begin
      return (not Nonblocking_Subprograms_Set.Contains (EN));
      --  Analysis of the call graph for potentially blocking calls is
      --  temprorarily disabled, since the created call graph is not yet
      --  complete.
      --
      --  The call graph needs to be created for all callable entities
      --  (i.e. procedures, functions and entries) of the current compilation
      --  unit; currently it is only created for those callable entities that
      --  have a GG (generated globals) entry in the ALI file created in phase
      --  1.
      --
      --  Once the call graph is fixed, the return statement needs to be
      --  extended with
      --    or else Calls_Potentially_Blocking_Subprogram;
   end Is_Potentially_Blocking;

   ---------------------
   -- Tasking_Objects --
   ---------------------

   function Tasking_Objects
     (Kind : Tasking_Info_Kind;
      Subp : Entity_Name)
      return Name_Sets.Set
   is
      C : constant Name_Graphs.Cursor := Tasking_Info_Bag (Kind).Find (Subp);
   begin
      return (if Has_Element (C)
              then Element (C)
              else Name_Sets.Empty_Set);
   end Tasking_Objects;

end Flow_Generated_Globals;
