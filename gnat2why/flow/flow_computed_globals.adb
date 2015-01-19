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

with Ada.Containers.Ordered_Sets;
with Ada.Containers.Hashed_Sets;
with Ada.Text_IO;                 use Ada.Text_IO;
with Ada.Text_IO.Unbounded_IO;    use Ada.Text_IO.Unbounded_IO;
with Ada.Strings.Unbounded;       use Ada.Strings.Unbounded;

with AA_Util;                     use AA_Util;
with ALI;                         use ALI;
with Osint;                       use Osint;
with Osint.C;                     use Osint.C;
with Sem_Util;                    use Sem_Util;
with Lib.Util;                    use Lib.Util;
with Namet;                       use Namet;

with Output;                      use Output;

with Graph;
with Flow_Utility;                use Flow_Utility;

with Gnat2Why_Args;
with Gnat2Why.Nodes;              use Gnat2Why.Nodes;

with SPARK_Frame_Conditions;      use SPARK_Frame_Conditions;

package body Flow_Computed_Globals is

   --  Debug flags

   Debug_Print_Info_Sets_Read : constant Boolean := False;
   --  Enables printing of Info_Sets as read from ALI files

   Debug_Print_Global_Graph   : constant Boolean := True;
   --  Enables printing of the Global_Graph

   ----------------------------------------------------------------------

   use type Flow_Id_Sets.Set;
   use type Name_Set.Set;

   type Subprogram_Phase_1_Info is record
      Subprogram        : Entity_Name;

      Inputs_Proof      : Name_Set.Set;
      Inputs            : Name_Set.Set;
      Outputs           : Name_Set.Set;
      Proof_Calls       : Name_Set.Set;
      Definite_Calls    : Name_Set.Set;
      Conditional_Calls : Name_Set.Set;
      Local_Variables   : Name_Set.Set;
   end record;

   function Preceeds (A, B : Subprogram_Phase_1_Info) return Boolean
   is (A.Subprogram.all < B.Subprogram.all);

   package Info_Sets is new Ada.Containers.Ordered_Sets
     (Element_Type => Subprogram_Phase_1_Info,
      "<"          => Preceeds,
      "="          => "=");

   Info_Set : Info_Sets.Set;

   ----------------------------------------------------------------------

   type State_Phase_1_Info is record
      State             : Entity_Name;
      Constituents      : Name_Set.Set;
   end record;

   function Preceeds (A, B : State_Phase_1_Info) return Boolean
   is (A.State.all < B.State.all);

   package State_Info_Sets is new Ada.Containers.Ordered_Sets
     (Element_Type => State_Phase_1_Info,
      "<"          => Preceeds,
      "="          => "=");

   State_Info_Set : State_Info_Sets.Set;

   ----------------------------------------------------------------------
   --  Global_Id
   ----------------------------------------------------------------------

   type Global_Id_Kind is (Null_Kind,
                           --  Does not represent anything yet

                           Ins_Kind,
                           --  Represents subprogram's Ins

                           Outs_Kind,
                           --  Represents subprogram's Outs

                           Proof_Ins_Kind,
                           --  Represents subprogram's Proof_Ins

                           Variable_Kind
                           --  Represents a global variable
                          );

   type Global_Id is record
      Kind : Global_Id_Kind;
      Name : Entity_Name;
   end record;

   function "=" (Left, Right : Global_Id) return Boolean is
      (Left.Kind = Right.Kind and then Left.Name.all = Right.Name.all);
   --  Equality for Global_Id

   Null_Global_Id : constant Global_Id :=
     Global_Id'(Kind => Null_Kind,
                Name => Null_Entity_Name);

   -------------------
   -- Global_Graphs --
   -------------------

   package Global_Graphs is new Graph (Vertex_Key   => Global_Id,
                                       Edge_Colours => Edge_Colours,
                                       Null_Key     => Null_Global_Id,
                                       Test_Key     => "=");

   package Vertex_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Global_Graphs.Vertex_Id,
      Hash                => Global_Graphs.Vertex_Hash,
      Equivalent_Elements => Global_Graphs."=",
      "="                 => Global_Graphs."=");

   Global_Graph : Global_Graphs.T;

   use Global_Graphs;

   -----------------------
   -- Local subprograms --
   -----------------------

   function To_Name (E : Entity_Id) return Entity_Name;
   --  Takes an Entity_Id and returns the corresponding Entity_Name

   function To_Name_Set (S : Node_Sets.Set) return Name_Set.Set;
   --  Takes a set of Node_Ids and returns a set of Entity_Names

   procedure Print_Subprogram_Phase_1_Info (Info : Subprogram_Phase_1_Info);
   --  Prints all info related to a subprogram

   procedure Print_Global_Graph (Filename : String;
                                 G        : T);
   --  Writes a dot and pdf file for the Global_Graph

   -------------
   -- To_Name --
   -------------

   function To_Name (E : Entity_Id) return Entity_Name
   is (new String'(Unique_Name (E)));

   -----------------
   -- To_Name_Set --
   -----------------

   function To_Name_Set (S : Node_Sets.Set) return Name_Set.Set is
      Rv : Name_Set.Set := Name_Set.Empty_Set;
   begin
      for E of S loop
         Rv.Insert (To_Name (E));
      end loop;
      return Rv;
   end To_Name_Set;

   -----------------------------------
   -- Print_Subprogram_Phase_1_Info --
   -----------------------------------

   procedure Print_Subprogram_Phase_1_Info (Info : Subprogram_Phase_1_Info) is
   begin
      Write_Line ("Subprogram " & Info.Subprogram.all);

      Write_Line ("Proof_Ins        :");
      for Name of Info.Inputs_Proof loop
         Write_Line ("   " & Name.all);
      end loop;

      Write_Line ("Inputs           :");
      for Name of Info.Inputs loop
         Write_Line ("   " & Name.all);
      end loop;

      Write_Line ("Outputs          :");
      for Name of Info.Outputs loop
         Write_Line ("   " & Name.all);
      end loop;

      Write_Line ("Proof calls      :");
      for Name of Info.Proof_Calls loop
         Write_Line ("   " & Name.all);
      end loop;

      Write_Line ("Definite calls   :");
      for Name of Info.Definite_Calls loop
         Write_Line ("   " & Name.all);
      end loop;

      Write_Line ("Conditional calls:");
      for Name of Info.Conditional_Calls loop
         Write_Line ("   " & Name.all);
      end loop;

      Write_Line ("Local variables  :");
      for Name of Info.Local_Variables loop
         Write_Line ("   " & Name.all);
      end loop;
   end Print_Subprogram_Phase_1_Info;

   ------------------------
   -- Print_Global_Graph --
   ------------------------

   procedure Print_Global_Graph (Filename : String;
                                 G        : T)
   is
      function NDI
        (G : T'Class;
         V : Vertex_Id) return Node_Display_Info;
      --  Pretty-printing for each vertex in the dot output.

      function EDI
        (G      : T'Class;
         A      : Vertex_Id;
         B      : Vertex_Id;
         Marked : Boolean;
         Colour : Edge_Colours) return Edge_Display_Info;
      --  Pretty-printing for each edge in the dot output.

      ---------
      -- NDI --
      ---------

      function NDI
        (G : T'Class;
         V : Vertex_Id) return Node_Display_Info
      is
         G_Id  : constant Global_Id := G.Get_Key (V);

         Shape : constant Node_Shape_T := (if G_Id.Kind = Variable_Kind
                                           then Shape_Oval
                                           else Shape_Box);

         Label : constant String :=
           (case G_Id.Kind is
              when Proof_Ins_Kind => G_Id.Name.all & "'Proof_Ins",
              when Ins_Kind       => G_Id.Name.all & "'Ins",
              when Outs_Kind      => G_Id.Name.all & "'Outs",
              when Variable_Kind  => G_Id.Name.all,
              when Null_Kind      => "");

         Rv : constant Node_Display_Info := Node_Display_Info'
           (Show   => True,
            Shape  => Shape,
            Colour => Null_Unbounded_String,
            Label  => To_Unbounded_String (Label));
      begin
         return Rv;
      end NDI;

      ---------
      -- EDI --
      ---------

      function EDI
        (G      : T'Class;
         A      : Vertex_Id;
         B      : Vertex_Id;
         Marked : Boolean;
         Colour : Edge_Colours) return Edge_Display_Info
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

   -------------------------
   -- GG_Write_Initialize --
   -------------------------

   procedure GG_Write_Initialize
   is
   begin
      Open_Output_Library_Info;
      Info_Set := Info_Sets.Empty_Set;
      State_Info_Set := State_Info_Sets.Empty_Set;

      Current_Mode := GG_Write_Mode;
   end GG_Write_Initialize;

   ---------------------------
   -- GG_Write_Package_Info --
   ---------------------------

   procedure GG_Write_Package_Info (DM : Dependency_Maps.Map) is
   begin
      for S in DM.Iterate loop
         declare
            State        : constant Entity_Name :=
              To_Name (Get_Direct_Mapping_Id (Dependency_Maps.Key (S)));

            Constituents : constant Name_Set.Set :=
              To_Name_Set (To_Node_Set (Dependency_Maps.Element (S)));

            State_Info   : constant State_Phase_1_Info :=
              State_Phase_1_Info'(State        => State,
                                  Constituents => Constituents);
         begin
            State_Info_Set.Insert (State_Info);
         end;
      end loop;
   end GG_Write_Package_Info;

   ------------------------------
   -- GG_Write_Subprogram_Info --
   ------------------------------

   procedure GG_Write_Subprogram_Info
     (E                 : Entity_Id;
      Inputs_Proof      : Node_Sets.Set;
      Inputs            : Node_Sets.Set;
      Outputs           : Node_Sets.Set;
      Proof_Calls       : Node_Sets.Set;
      Definite_Calls    : Node_Sets.Set;
      Conditional_Calls : Node_Sets.Set;
      Local_Variables   : Node_Sets.Set)
   is
   begin
      Info_Set.Insert ((To_Name (E),
                        Inputs_Proof      => To_Name_Set (Inputs_Proof),
                        Inputs            => To_Name_Set (Inputs),
                        Outputs           => To_Name_Set (Outputs),
                        Proof_Calls       => To_Name_Set (Proof_Calls),
                        Definite_Calls    => To_Name_Set (Definite_Calls),
                        Conditional_Calls => To_Name_Set (Conditional_Calls),
                        Local_Variables   => To_Name_Set (Local_Variables)));
   end GG_Write_Subprogram_Info;

   procedure GG_Write_Subprogram_Info
     (E                 : Entity_Id;
      Inputs_Proof      : Name_Set.Set;
      Inputs            : Name_Set.Set;
      Outputs           : Name_Set.Set;
      Proof_Calls       : Name_Set.Set;
      Definite_Calls    : Name_Set.Set;
      Conditional_Calls : Name_Set.Set;
      Local_Variables   : Name_Set.Set)
   is
   begin
      Info_Set.Insert ((To_Name (E),
                        Inputs_Proof      => Inputs_Proof,
                        Inputs            => Inputs,
                        Outputs           => Outputs,
                        Proof_Calls       => Proof_Calls,
                        Definite_Calls    => Definite_Calls,
                        Conditional_Calls => Conditional_Calls,
                        Local_Variables   => Local_Variables));
   end GG_Write_Subprogram_Info;

   -----------------------
   -- GG_Write_Finalize --
   -----------------------

   procedure GG_Write_Finalize
   is
      procedure Write_Name_Set (S : Name_Set.Set);

      --------------------
      -- Write_Name_Set --
      --------------------

      procedure Write_Name_Set (S : Name_Set.Set)
      is
      begin
         for N of S loop
            Write_Info_Char (' ');
            Write_Info_Str (N.all);
         end loop;
      end Write_Name_Set;
   begin
      for State_Info of State_Info_Set loop
         Write_Info_Str ("GG AS ");
         Write_Info_Str (State_Info.State.all);
         Write_Name_Set (State_Info.Constituents);
         Write_Info_Terminate;
      end loop;

      for Info of Info_Set loop
         Write_Info_Str ("GG S ");
         Write_Info_Str (Info.Subprogram.all);
         Write_Info_Terminate;

         Write_Info_Str ("GG VP");
         Write_Name_Set (Info.Inputs_Proof);
         Write_Info_Terminate;

         Write_Info_Str ("GG VI");
         Write_Name_Set (Info.Inputs);
         Write_Info_Terminate;

         Write_Info_Str ("GG VO");
         Write_Name_Set (Info.Outputs);
         Write_Info_Terminate;

         Write_Info_Str ("GG CP");
         Write_Name_Set (Info.Proof_Calls);
         Write_Info_Terminate;

         Write_Info_Str ("GG CD");
         Write_Name_Set (Info.Definite_Calls);
         Write_Info_Terminate;

         Write_Info_Str ("GG CC");
         Write_Name_Set (Info.Conditional_Calls);
         Write_Info_Terminate;

         Write_Info_Str ("GG LV");
         Write_Name_Set (Info.Local_Variables);
         Write_Info_Terminate;
      end loop;

      Close_Output_Library_Info;
      Current_Mode := GG_No_Mode;
   end GG_Write_Finalize;

   -------------
   -- GG_Read --
   -------------

   procedure GG_Read (GNAT_Root : Node_Id) is
      All_Globals           : Name_Set.Set := Name_Set.Empty_Set;
      --  Contains all global variables

      GG_Subprograms        : Name_Set.Set := Name_Set.Empty_Set;
      --  Contains all subprograms for which a GG entry exists

      All_Subprograms       : Name_Set.Set := Name_Set.Empty_Set;
      --  Contains all subprograms that we know of, even if a
      --  GG entry does not exist for them.

      All_Other_Subprograms : Name_Set.Set := Name_Set.Empty_Set;
      --  Contains all subprograms for which a GG entry does not
      --  exist.

      procedure Add_All_Edges;
      --  Reads the populated Info_Set and generates all the edges of
      --  the Global_Graph.

      procedure Create_All_Vertices;
      --  Creates all the vertices of the Global_Graph

      procedure Load_GG_Info_From_ALI (ALI_File_Name : File_Name_Type);
      --  Gets the GG info from an ALI file and stores them in the
      --  Info_Set table.
      --
      --  The info that we read look as follows:
      --
      --  GG AS test__state test__g
      --  GG S test__proc
      --  GG VP test__proof_var
      --  GG VI test__g test__g2
      --  GG VO test__g
      --  GG CP test__ghost_func_a test__ghost_func_b
      --  GG CD test__proc_2 test__proc__nested_proc
      --  GG CC test__proc_3
      --  GG LV test__proc__nested_proc__v

      procedure Remove_Edges_To_Local_Variables;
      --  Removes edges between subprograms and their local variables

      procedure Edit_Proof_Ins;
      --  A variable cannot be simultaneously a Proof_In and an Input
      --  of a subprogram. In this case we need to remove the Proof_In
      --  edge. Furthermore, a variable cannot be simultaneously a
      --  Proof_In and an Output (but not an input). In this case we
      --  need to change the Proof_In variable into an Input.

      -------------------
      -- Add_All_Edges --
      -------------------

      procedure Add_All_Edges is
         G_Ins, G_Outs, G_Proof_Ins : Global_Id;

         procedure Add_Edge (G1, G2 : Global_Id);
         --  Adds an edge between the vertices V1 and V2 that
         --  correspond to G1 and G2 (V1 --> V2). The edge has the
         --  default colour.

         --------------
         -- Add_Edge --
         --------------

         procedure Add_Edge (G1, G2 : Global_Id) is
         begin
            Global_Graph.Add_Edge (G1, G2, EC_Default);
         end Add_Edge;
      begin
         --  Go through everything in Info_Set and add edges
         for Info of Info_Set loop
            G_Ins       := Global_Id'(Kind => Ins_Kind,
                                      Name => Info.Subprogram);

            G_Outs      := Global_Id'(Kind => Outs_Kind,
                                      Name => Info.Subprogram);

            G_Proof_Ins := Global_Id'(Kind => Proof_Ins_Kind,
                                      Name => Info.Subprogram);

            --  Connecting the subprogram's Proof_In variables to the
            --  subprogram's Proof_Ins vertex.
            for Input_Proof of Info.Inputs_Proof loop
               Add_Edge (G_Proof_Ins,
                         Global_Id'(Kind => Variable_Kind,
                                    Name => Input_Proof));
            end loop;

            --  Connecting the subprogram's Input variables to the
            --  subprogram's Ins vertex.
            for Input of Info.Inputs loop
               Add_Edge (G_Ins,
                         Global_Id'(Kind => Variable_Kind,
                                    Name => Input));
            end loop;

            --  Connecting the subprogram's Output variables to the
            --  subprogram's Outputs vertex.
            for Output of Info.Outputs loop
               Add_Edge (G_Outs,
                         Global_Id'(Kind => Variable_Kind,
                                    Name => Output));
            end loop;

            --  Connecting the subprogram's Proof_Ins vertex to the
            --  callee's Ins and Proof_Ins vertices.
            for Proof_Call of Info.Proof_Calls loop
               Add_Edge (G_Proof_Ins,
                         Global_Id'(Kind => Proof_Ins_Kind,
                                    Name => Proof_Call));

               Add_Edge (G_Proof_Ins,
                         Global_Id'(Kind => Ins_Kind,
                                    Name => Proof_Call));
            end loop;

            --  Connecting the subprogram's Proof_Ins, Ins and Outs
            --  vertices respectively to the callee's Proof_Ins, Ins
            --  and Outs vertices.
            for Definite_Call of Info.Definite_Calls loop
               Add_Edge (G_Proof_Ins,
                         Global_Id'(Kind => Proof_Ins_Kind,
                                    Name => Definite_Call));

               Add_Edge (G_Ins,
                         Global_Id'(Kind => Ins_Kind,
                                    Name => Definite_Call));

               Add_Edge (G_Outs,
                         Global_Id'(Kind => Outs_Kind,
                                    Name => Definite_Call));
            end loop;

            --  As above but we also add an edge from the subprogram's
            --  Ins vertex to the callee's Outs vertex.
            for Conditional_Call of Info.Conditional_Calls loop
               Add_Edge (G_Proof_Ins,
                         Global_Id'(Kind => Proof_Ins_Kind,
                                    Name => Conditional_Call));

               Add_Edge (G_Ins,
                         Global_Id'(Kind => Ins_Kind,
                                    Name => Conditional_Call));

               Add_Edge (G_Ins,
                         Global_Id'(Kind => Outs_Kind,
                                    Name => Conditional_Call));

               Add_Edge (G_Outs,
                         Global_Id'(Kind => Outs_Kind,
                                    Name => Conditional_Call));
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
               Unreferenced : Boolean;

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
                                To_Name (Get_Direct_Mapping_Id (F))
                             elsif F.Kind = Magic_String then
                                F.Name
                             else
                                raise Program_Error);
                     G   := Global_Id'(Kind => Variable_Kind,
                                       Name => Nam);

                     if not Global_Graph.Edge_Exists (From, G) then
                        Add_Edge (From, G);
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

               if Subprogram /= Empty then
                  Get_Globals (Subprogram => Subprogram,
                               Scope      => Get_Flow_Scope (Subprogram),
                               Classwide  => False,
                               Proof_Ins  => FS_Proof_Ins,
                               Reads      => FS_Reads,
                               Writes     => FS_Writes,
                               Computed   => Unreferenced);

                  Add_Edges_For_FS (FS_Proof_Ins, G_Proof_Ins);
                  Add_Edges_For_FS (FS_Reads, G_Ins);
                  Add_Edges_For_FS (FS_Writes, G_Outs);
               end if;
            end;
         end loop;

         --  Close graph
         Global_Graph.Close;
      end Add_All_Edges;

      -------------------------
      -- Create_All_Vertices --
      -------------------------

      procedure Create_All_Vertices is
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
            end;
         end loop;

         --  Lastly we have to create vertices for variables that come
         --  from the Get_Globals function.
         for N of All_Other_Subprograms loop
            declare
               Subprogram   : constant Entity_Id := Find_Entity (N);
               FS_Proof_Ins : Flow_Id_Sets.Set;
               FS_Reads     : Flow_Id_Sets.Set;
               FS_Writes    : Flow_Id_Sets.Set;
               Unreferenced : Boolean;

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
                                To_Name (Get_Direct_Mapping_Id (F))
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
                               Writes     => FS_Writes,
                               Computed   => Unreferenced);

                  Create_Vertices_For_FS (FS_Proof_Ins);
                  Create_Vertices_For_FS (FS_Reads);
                  Create_Vertices_For_FS (FS_Writes);
               end if;
            end;
         end loop;
      end Create_All_Vertices;

      ---------------------------
      -- Load_GG_Info_From_ALI --
      ---------------------------

      procedure Load_GG_Info_From_ALI (ALI_File_Name : File_Name_Type) is
         ALI_File_Name_Str : constant String :=
           Name_String (Name_Id (Full_Lib_File_Name (ALI_File_Name)));

         ALI_File          : Ada.Text_IO.File_Type;
         Line              : Unbounded_String;

         procedure Parse_Record;
         --  Parses a GG record from the ALI file and if no problems
         --  occurred it adds it to Info_Set.

         ------------------
         -- Parse_Record --
         ------------------

         procedure Parse_Record is
            type Line_Found_T is array (1 .. 8) of Boolean;
            --  This array represents whether we have found a line
            --  of the following format while populating the record.
            --  The order is as follow:
            --
            --  array slot 1 is True if we have found "GG S *"
            --  array slot 2 is True if we have found "GG VP *"
            --  array slot 3 is True if we have found "GG VI *"
            --  array slot 4 is True if we have found "GG VO *"
            --  array slot 5 is True if we have found "GG CP *"
            --  array slot 6 is True if we have found "GG CD *"
            --  array slot 7 is True if we have found "GG CC *"
            --  array slot 8 is True if we have found "GG LV *"

            Line_Found : Line_Found_T := Line_Found_T'(others => False);
            --  Initially we haven't found anything

            New_Info   : Subprogram_Phase_1_Info;

            procedure Check_GG_Format;
            --  Checks if the line start with "GG "

            function Get_Names_From_Line return Name_Set.Set;
            --  Returns a set of all names appearing in a line

            ---------------------
            -- Check_GG_Format --
            ---------------------

            procedure Check_GG_Format is
            begin
               if Length (Line) <= 3 or else
                 Slice (Line, 1, 3) /= "GG "
               then
                  --  Either the ali file has been tampered with
                  --  or we are dealing with a new kind of line
                  --  that we are not aware of.
                  raise Program_Error;
               end if;
            end Check_GG_Format;

            -------------------------
            -- Get_Names_From_Line --
            -------------------------

            function Get_Names_From_Line return Name_Set.Set is
               Names_In_Line : Name_Set.Set :=
                 Name_Set.Empty_Set;

               Start_Of_Word : Natural      := 7;
               End_Of_Word   : Natural;
            begin
               if Length (Line) = 5 then
                  --  There are no names here. Return the empty set.
                  return Names_In_Line;
               end if;

               while Start_Of_Word < Length (Line) loop
                  End_Of_Word := Start_Of_Word;

                  while End_Of_Word < Length (Line)
                    and then Element (Line, End_Of_Word) > ' '
                  loop
                     End_Of_Word := End_Of_Word + 1;
                  end loop;

                  --  If we have not reached the end of the line then
                  --  we have read one character too many.
                  if End_Of_Word < Length (Line) then
                     End_Of_Word := End_Of_Word - 1;
                  end if;

                  declare
                     EN : constant Entity_Name :=
                       new String'(Slice (Line,
                                          Start_Of_Word,
                                          End_Of_Word));
                  begin
                     Names_In_Line.Insert (EN);
                  end;

                  Start_Of_Word := End_Of_Word + 2;
               end loop;

               return Names_In_Line;
            end Get_Names_From_Line;

         begin
            --  We special case lines that contain info about state
            --  abstractions.
            if Length (Line) > 6
              and then Slice (Line, 1, 6) = "GG AS "
            then
               declare
                  State         : Entity_Name;
                  Constituents  : Name_Set.Set := Get_Names_From_Line;
                  Start_Of_Word : constant Natural := 7;
                  End_Of_Word   : Natural := 7;
               begin
                  while End_Of_Word < Length (Line)
                    and then Element (Line, End_Of_Word) > ' '
                  loop
                     End_Of_Word := End_Of_Word + 1;
                  end loop;

                  --  If we have not reached the end of the line then
                  --  we have read one character too many.
                  if End_Of_Word < Length (Line) then
                     End_Of_Word := End_Of_Word - 1;
                  end if;

                  State := new String'(Slice (Line,
                                              Start_Of_Word,
                                              End_Of_Word));

                  Constituents.Exclude (State);

                  State_Info_Set.Include
                    (State_Phase_1_Info'(State        => State,
                                         Constituents => Constituents));
               end;

               --  Go to the next line
               if not End_Of_File (ALI_File) then
                  Get_Line (ALI_File, Line);
               end if;
               return;
            end if;

            while (for some I in 1 .. 8 => Line_Found (I) = False) loop
               Check_GG_Format;

               if Length (Line) >= 6 and then
                 Slice (Line, 4, 5) = "S "
               then
                  --  Line format: GG S *
                  if Line_Found (1) then
                     --  We have already processed this line.
                     --  Something is wrong with the ali file.
                     raise Program_Error;
                  end if;

                  Line_Found (1) := True;

                  declare
                     EN : constant Entity_Name :=
                       new String'(Slice (Line,
                                          6,
                                          Length (Line)));
                  begin
                     New_Info.Subprogram := EN;
                     GG_Subprograms.Include (EN);
                  end;

               elsif Length (Line) >= 5 then
                  if Slice (Line, 4, 5) = "VP" then
                     if Line_Found (2) then
                        raise Program_Error;
                     end if;

                     Line_Found (2) := True;
                     New_Info.Inputs_Proof := Get_Names_From_Line;
                     All_Globals.Union (Get_Names_From_Line);

                  elsif Slice (Line, 4, 5) = "VI" then
                     if Line_Found (3) then
                        raise Program_Error;
                     end if;

                     Line_Found (3) := True;
                     New_Info.Inputs := Get_Names_From_Line;
                     All_Globals.Union (Get_Names_From_Line);

                  elsif Slice (Line, 4, 5) = "VO" then
                     if Line_Found (4) then
                        raise Program_Error;
                     end if;

                     Line_Found (4) := True;
                     New_Info.Outputs := Get_Names_From_Line;
                     All_Globals.Union (Get_Names_From_Line);

                  elsif Slice (Line, 4, 5) = "CP" then
                     if Line_Found (5) then
                        raise Program_Error;
                     end if;

                     Line_Found (5) := True;
                     New_Info.Proof_Calls := Get_Names_From_Line;

                  elsif Slice (Line, 4, 5) = "CD" then
                     if Line_Found (6) then
                        raise Program_Error;
                     end if;

                     Line_Found (6) := True;
                     New_Info.Definite_Calls := Get_Names_From_Line;

                  elsif Slice (Line, 4, 5) = "CC" then
                     if Line_Found (7) then
                        raise Program_Error;
                     end if;

                     Line_Found (7) := True;
                     New_Info.Conditional_Calls := Get_Names_From_Line;

                  elsif Slice (Line, 4, 5) = "LV" then
                     if Line_Found (8) then
                        raise Program_Error;
                     end if;

                     Line_Found (8) := True;
                     New_Info.Local_Variables := Get_Names_From_Line;
                     All_Globals.Union (Get_Names_From_Line);

                  else
                     --  Unexpected type of line. Something is wrong
                     --  with the ALI file.
                     raise Program_Error;
                  end if;

               else
                  --  Something is wrong with the ALI file
                  raise Program_Error;
               end if;

               --  Go to the next line
               if not End_Of_File (ALI_File) then
                  Get_Line (ALI_File, Line);
               elsif (for some I in 1 .. 8 => Line_Found (I) = False) then
                  --  We reached the end of the file and our New_Info
                  --  is not yet complete. Something is missing from
                  --  the ALI file.
                  raise Program_Error;
               end if;
            end loop;

            --  Add New_Info to Info_Set
            Info_Set.Include (New_Info);
         end Parse_Record;

      begin
         Open (ALI_File, In_File, ALI_File_Name_Str);

         loop
            if End_Of_File (ALI_File) then
               Close (ALI_File);
               return;
            end if;

            Get_Line (ALI_File, Line);
            if Length (Line) > 0 and then Element (Line, 1) = 'G' then
               exit;
            end if;
         end loop;

         --  We have now reached the "GG" section of the ALI file
         while not End_Of_File (ALI_File) loop
            Parse_Record;
         end loop;

         Close (ALI_File);
      end Load_GG_Info_From_ALI;

      -------------------------------------
      -- Remove_Edges_To_Local_Variables --
      -------------------------------------

      procedure Remove_Edges_To_Local_Variables is

         procedure Remove_Local_Variables_From_Set
           (Start : Vertex_Id;
            Info  : Subprogram_Phase_1_Info);
         --  Removes all edges starting from Start and leading to a
         --  local variable or a variable that is local to any of the
         --  subprograms called by this subprogram.

         -------------------------------------
         -- Remove_Local_Variables_From_Set --
         -------------------------------------

         procedure Remove_Local_Variables_From_Set
           (Start : Vertex_Id;
            Info  : Subprogram_Phase_1_Info)
         is
            G                      : Global_Id;
            VS                     : Vertex_Sets.Set := Vertex_Sets.Empty_Set;
            All_Subprograms_Called : Name_Set.Set := Name_Set.Empty_Set;
            All_Local_Variables    : Name_Set.Set := Info.Local_Variables;
         begin
            for V of Global_Graph.Get_Collection (Start, Out_Neighbours) loop
               if Global_Graph.Get_Key (V).Kind in Proof_Ins_Kind |
                                                   Ins_Kind       |
                                                   Outs_Kind
               then
                  All_Subprograms_Called.Include
                    (Global_Graph.Get_Key (V).Name);
               end if;
            end loop;

            for I of Info_Set loop
               if (for some Callee of All_Subprograms_Called =>
                     I.Subprogram.all = Callee.all)
               then
                  All_Local_Variables.Union (I.Local_Variables);
               end if;
            end loop;

            for V of Global_Graph.Get_Collection (Start, Out_Neighbours) loop
               G := Global_Graph.Get_Key (V);

               if (for some N of All_Local_Variables => N.all = G.Name.all)
               then
                  VS.Include (V);
               end if;
            end loop;

            for V of VS loop
               Global_Graph.Remove_Edge (Start, V);
            end loop;
         end Remove_Local_Variables_From_Set;

      begin
         for Info of Info_Set loop
            declare
               G_Ins       : constant Global_Id :=
                 Global_Id'(Kind => Ins_Kind,
                            Name => Info.Subprogram);

               G_Outs      : constant Global_Id :=
                 Global_Id'(Kind => Outs_Kind,
                            Name => Info.Subprogram);

               G_Proof_Ins : constant Global_Id :=
                 Global_Id'(Kind => Proof_Ins_Kind,
                            Name => Info.Subprogram);

               V_Ins       : constant Vertex_Id :=
                 Global_Graph.Get_Vertex (G_Ins);

               V_Outs      : constant Vertex_Id :=
                 Global_Graph.Get_Vertex (G_Outs);

               V_Proof_Ins : constant Vertex_Id :=
                 Global_Graph.Get_Vertex (G_Proof_Ins);
            begin
               Remove_Local_Variables_From_Set (V_Ins, Info);
               Remove_Local_Variables_From_Set (V_Outs, Info);
               Remove_Local_Variables_From_Set (V_Proof_Ins, Info);
            end;
         end loop;
      end Remove_Edges_To_Local_Variables;

      --------------------
      -- Edit_Proof_Ins --
      --------------------

      procedure Edit_Proof_Ins is
         function Get_Variable_Neighbours
           (Start : Vertex_Id)
            return Vertex_Sets.Set;
         --  Returns a set of all Neighbours of Start that correspond
         --  to variables.

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
      begin
         for Info of Info_Set loop
            declare
               G_Ins       : constant Global_Id :=
                 Global_Id'(Kind => Ins_Kind,
                            Name => Info.Subprogram);

               G_Outs      : constant Global_Id :=
                 Global_Id'(Kind => Outs_Kind,
                            Name => Info.Subprogram);

               G_Proof_Ins : constant Global_Id :=
                 Global_Id'(Kind => Proof_Ins_Kind,
                            Name => Info.Subprogram);

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
                        Global_Graph.Add_Edge (V_Ins, V, EC_Default);
                     end if;

                     Global_Graph.Remove_Edge (V_Proof_Ins, V);
                  end if;
               end loop;
            end;
         end loop;
      end Edit_Proof_Ins;

   begin  --  Beginning of GG_Read
      Current_Mode := GG_Read_Mode;

      --  Go through all ALI files and populate the Info_Set
      for Index in ALIs.First .. ALIs.Last loop
         Load_GG_Info_From_ALI (ALIs.Table (Index).Afile);
      end loop;

      if Debug_Print_Info_Sets_Read then
         --  Print all GG related info gathered from the ALI files.
         Write_Line ("GG info as read from ALI files:");

         for Info of Info_Set loop
            Write_Eol;
            Print_Subprogram_Phase_1_Info (Info);
         end loop;

         for State_Info of State_Info_Set loop
            Write_Eol;
            Write_Line ("Abstract state " & State_Info.State.all);

            Write_Line ("Constituents     :");
            for Name of State_Info.Constituents loop
               Write_Line ("   " & Name.all);
            end loop;
         end loop;
      end if;

      --  Populated the All_Subprograms set
      All_Subprograms := GG_Subprograms;
      for Info of Info_Set loop
         --  Add all subprograms mentioned in the proof calls
         All_Subprograms.Union (Info.Proof_Calls);
         --  Add all subprograms mentioned in the definite calls
         All_Subprograms.Union (Info.Definite_Calls);
         --  Add all subprograms mentioned in the conditional calls
         All_Subprograms.Union (Info.Conditional_Calls);
      end loop;

      --  Populated the All_Other_Subprograms set
      All_Other_Subprograms := All_Subprograms - GG_Subprograms;

      --  Initialize Global_Graph
      Global_Graph := Global_Graphs.Create;

      --  Create all vertices of the Global_Graph
      Create_All_Vertices;

      --  Add all edges in the Global_Graph
      Add_All_Edges;

      --  Remove edges between a subprogram and its local variables
      Remove_Edges_To_Local_Variables;

      --  Edit Proof_Ins
      Edit_Proof_Ins;

      if Debug_Print_Global_Graph then
         declare
            Filename : constant String :=
              Spec_File_Name_Without_Suffix
                (Enclosing_Comp_Unit_Node (GNAT_Root)) & "_Globals_Graph";
         begin
            Print_Global_Graph (Filename => Filename,
                                G        => Global_Graph);
         end;
      end if;

   end GG_Read;

   --------------
   -- GG_Exist --
   --------------

   function GG_Exist (E : Entity_Id) return Boolean is
      Name : constant Entity_Name := new String'(Unique_Name (E));
   begin
      return (for some Info of Info_Set => Name.all = Info.Subprogram.all);
   end GG_Exist;

   -----------------------
   -- GG_Has_Refinement --
   -----------------------

   function GG_Has_Refinement (EN : Entity_Name) return Boolean is
   begin
      return (for some S of State_Info_Set => S.State.all = EN.all);
   end GG_Has_Refinement;

   -----------------------
   -- GG_Is_Constituent --
   -----------------------

   function GG_Is_Constituent (EN : Entity_Name) return Boolean is
   begin
      return (for some S of State_Info_Set =>
                (for some C of S.Constituents => EN.all = C.all));
   end GG_Is_Constituent;

   -------------------------
   -- GG_Get_Constituents --
   -------------------------

   function GG_Get_Constituents (EN : Entity_Name) return Name_Set.Set is
   begin
      for S of State_Info_Set loop
         if S.State.all = EN.all then
            return S.Constituents;
         end if;
      end loop;

      return Name_Set.Empty_Set;
   end GG_Get_Constituents;

   ------------------------
   -- GG_Enclosing_State --
   ------------------------

   function GG_Enclosing_State (EN : Entity_Name) return Entity_Name is
   begin
      for S of State_Info_Set loop
         for C of S.Constituents loop
            if EN.all = C.all then
               return S.State;
            end if;
         end loop;
      end loop;

      return Null_Entity_Name;
   end GG_Enclosing_State;

   ---------------------
   -- GG_Fully_Refine --
   ---------------------

   function GG_Fully_Refine (EN : Entity_Name) return Name_Set.Set is
      NS       : Name_Set.Set;
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

   --------------------
   -- GG_Get_Globals --
   --------------------

   procedure GG_Get_Globals (E           : Entity_Id;
                             S           : Flow_Scope;
                             Proof_Reads : out Flow_Id_Sets.Set;
                             Reads       : out Flow_Id_Sets.Set;
                             Writes      : out Flow_Id_Sets.Set)
   is
      MR_Proof_Reads  : Name_Set.Set := Name_Set.Empty_Set;
      MR_Reads        : Name_Set.Set := Name_Set.Empty_Set;
      MR_Writes       : Name_Set.Set := Name_Set.Empty_Set;
      --  The above 3 sets will contain the most refined views of
      --  their respective globals.

      Subprogram_Name : constant Entity_Name := new String'(Unique_Name (E));
      --  Holds the Entity_Name of the subprogram

      G_Proof_Ins     : constant Global_Id :=
        Global_Id'(Kind => Proof_Ins_Kind,
                   Name => Subprogram_Name);
      G_Ins           : constant Global_Id :=
        Global_Id'(Kind => Ins_Kind,
                   Name => Subprogram_Name);
      G_Outs          : constant Global_Id :=
        Global_Id'(Kind => Outs_Kind,
                   Name => Subprogram_Name);
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

      procedure Up_Project
        (Most_Refined      : Name_Set.Set;
         Final_View        : out Name_Set.Set;
         Processing_Writes : Boolean := False);
      --  Distinguishes between simple vars and constituents. For
      --  constituents, it checks if they are visible and if they are
      --  NOT we check if their enclosing state is. If the enclosing
      --  state is visible then return that (otherwise repeat the
      --  process). When Processing_Writes is set, we also check if
      --  all constituents are used and if they are not we need also
      --  add them on the Reads set.

      ----------------
      -- Up_Project --
      ----------------

      procedure Up_Project
        (Most_Refined      : Name_Set.Set;
         Final_View        : out Name_Set.Set;
         Processing_Writes : Boolean := False)
      is
         Abstract_States : Name_Set.Set := Name_Set.Empty_Set;
      begin
         --  Initializing Final_View to empty
         Final_View := Name_Set.Empty_Set;

         for N of Most_Refined loop
            if GG_Enclosing_State (N) /= Null_Entity_Name and then
              (Find_Entity (N) = Empty or else
                 not Is_Visible (Find_Entity (N), S))
            then
               declare
                  Var               : Entity_Name :=
                    (if Find_Entity (N) /= Empty
                       and then Is_Visible (Find_Entity (N), S)
                     then N
                     else GG_Enclosing_State (N));
                  ES                : Entity_Name := GG_Enclosing_State (N);
                  Is_Abstract_State : Boolean     := False;
               begin
                  while Find_Entity (ES) = Empty or else
                    not Is_Visible (Find_Entity (ES), S)
                  loop
                     Is_Abstract_State := True;
                     Var := ES;

                     if GG_Enclosing_State (ES) /= Null_Entity_Name then
                        ES := GG_Enclosing_State (ES);
                     else
                        --  We cannot go any further up and we still
                        --  do not have visibility of the variable or
                        --  state abstraction that we are making use
                        --  of. This means that the user has neglected
                        --  to provide some state abstraction and the
                        --  refinement thereof. Unfortunately, we
                        --  might now refer to a variable or state
                        --  that the caller should not have vision of.
                        exit;
                     end if;
                  end loop;

                  Final_View.Include (Var);

                  --  We add the enclosing abstract state that we just
                  --  added to the Final_View set to the
                  --  Abstract_States set.
                  if Is_Abstract_State then
                     Abstract_States.Include (Var);
                  end if;
               end;
            else
               --  Add variables that are directly visible or do not
               --  belong to any state abstraction to the Final_View
               --  set.
               Final_View.Include (N);
            end if;
         end loop;

         --  If we Write some but not all constituents of a state
         --  abstraction then this state abstraction is also a Read.
         if Processing_Writes then
            for AS of Abstract_States loop
               declare
                  Constituents : constant Name_Set.Set :=
                    GG_Fully_Refine (AS);
               begin
                  if not (for all C of Constituents =>
                            Most_Refined.Contains (C))
                  then
                     Reads.Include (Get_Flow_Id (AS, In_View));
                  end if;
               end;
            end loop;
         end if;
      end Up_Project;

   begin
      --  Initialize the Proof_Reads, Reads and Writes sets
      Proof_Reads := Flow_Id_Sets.Empty_Set;
      Reads       := Flow_Id_Sets.Empty_Set;
      Writes      := Flow_Id_Sets.Empty_Set;

      --  Calculate MR_Proof_Reads, MR_Reads and MR_Writes
      declare
         function Calculate_MR (Start : Vertex_Id) return Name_Set.Set;
         --  Returns a set of all vertices that can be reached from
         --  Start and are of the Variable_Kind.

         ------------------
         -- Calculate_MR --
         ------------------

         function Calculate_MR (Start : Vertex_Id) return Name_Set.Set is
            NS : Name_Set.Set := Name_Set.Empty_Set;
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
         MR_Proof_Reads := Calculate_MR (V_Proof_Ins);
         MR_Reads       := Calculate_MR (V_Ins);
         MR_Writes      := Calculate_MR (V_Outs);
      end;

      --  Up project variables based on scope S and give Flow_Ids
      --  their correct views.
      declare
         Temp_NS : Name_Set.Set;

         function To_Flow_Id_Set
           (NS   : Name_Set.Set;
            View : Parameter_Variant)
            return Flow_Id_Sets.Set;
         --  Takes a Name_Set and returns a set of Flow_Id_Set

         --------------------
         -- To_Flow_Id_Set --
         --------------------

         function To_Flow_Id_Set
           (NS   : Name_Set.Set;
            View : Parameter_Variant)
            return Flow_Id_Sets.Set
         is
            FS : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
         begin
            for N of NS loop
               FS.Include (Get_Flow_Id (N, View));
            end loop;

            return FS;
         end To_Flow_Id_Set;

      begin
         Up_Project (Most_Refined => MR_Proof_Reads,
                     Final_View   => Temp_NS);
         Proof_Reads.Union (To_Flow_Id_Set (Temp_NS, In_View));

         Up_Project (Most_Refined => MR_Reads,
                     Final_View   => Temp_NS);
         Reads.Union (To_Flow_Id_Set (Temp_NS, In_View));

         Up_Project (Most_Refined      => MR_Writes,
                     Final_View        => Temp_NS,
                     Processing_Writes => True);
         Writes.Union (To_Flow_Id_Set (Temp_NS, Out_View));
      end;
   end GG_Get_Globals;

   ------------------------
   -- GG_Get_Proof_Reads --
   ------------------------

   function GG_Get_Proof_Reads
     (E : Entity_Id;
      S : Flow_Scope)
      return Flow_Id_Sets.Set
   is
      Proof_Reads, Reads, Writes : Flow_Id_Sets.Set;
   begin
      GG_Get_Globals (E,
                      S,
                      Proof_Reads,
                      Reads,
                      Writes);

      return Proof_Reads;
   end GG_Get_Proof_Reads;

   ------------------
   -- GG_Get_Reads --
   ------------------

   function GG_Get_Reads
     (E : Entity_Id;
      S : Flow_Scope)
      return Flow_Id_Sets.Set
   is
      Proof_Reads, Reads, Writes : Flow_Id_Sets.Set;
   begin
      GG_Get_Globals (E,
                      S,
                      Proof_Reads,
                      Reads,
                      Writes);

      return Reads;
   end GG_Get_Reads;

   ----------------------
   -- GG_Get_All_Reads --
   ----------------------

   function GG_Get_All_Reads
     (E : Entity_Id;
      S : Flow_Scope)
      return Flow_Id_Sets.Set
   is
   begin
      return GG_Get_Proof_Reads (E, S) or GG_Get_Reads (E, S);
   end GG_Get_All_Reads;

   -------------------
   -- GG_Get_Writes --
   -------------------

   function GG_Get_Writes
     (E : Entity_Id;
      S : Flow_Scope)
      return Flow_Id_Sets.Set
   is
      Proof_Reads, Reads, Writes : Flow_Id_Sets.Set;
   begin
      GG_Get_Globals (E,
                      S,
                      Proof_Reads,
                      Reads,
                      Writes);

      return Writes;
   end GG_Get_Writes;

end Flow_Computed_Globals;
