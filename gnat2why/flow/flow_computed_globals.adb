------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--               F L O W . C O M P U T E D _ G L O B A L S                  --
--                                                                          --
--                                B o d y                                   --
--                                                                          --
--               Copyright (C) 2014, Altran UK Limited                 --
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

with Gnat2Why_Args;
with Gnat2Why.Nodes;              use Gnat2Why.Nodes;

package body Flow_Computed_Globals is

   --  Debug flags

   Debug_Print_Info_Sets_Read : constant Boolean := False;
   --  Enables printing of Info_Sets as read from ALI files

   Debug_Print_Global_Graph   : constant Boolean := True;
   --  Enables printing of the Global_Graph

   ----------------------------------------------------------------------

   use type Flow_Id_Sets.Set;

   type Subprogram_Phase_1_Info is record
      Subprogram        : Entity_Name;

      Inputs_Proof      : Name_Set.Set;
      Inputs            : Name_Set.Set;
      Outputs           : Name_Set.Set;
      Proof_Calls       : Name_Set.Set;
      Definite_Calls    : Name_Set.Set;
      Conditional_Calls : Name_Set.Set;
   end record;

   function Preceeds (A, B : Subprogram_Phase_1_Info) return Boolean
   is (A.Subprogram.all < B.Subprogram.all);

   package Info_Sets is new Ada.Containers.Ordered_Sets
     (Element_Type => Subprogram_Phase_1_Info,
      "<"          => Preceeds,
      "="          => "=");

   Info_Set : Info_Sets.Set;

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

   Global_Graph : Global_Graphs.T;

   use Global_Graphs;

   -----------------------
   -- Local subprograms --
   -----------------------

   procedure Print_Subprogram_Phase_1_Info (Info : Subprogram_Phase_1_Info);
   --  Prints all info related to a subprogram

   procedure Print_Global_Graph (Filename : String;
                                 G        : T);
   --  Writes a dot and pdf file for the Global_Graph

   -----------------------------------
   -- Print_Subprogram_Phase_1_Info --
   -----------------------------------

   procedure Print_Subprogram_Phase_1_Info (Info : Subprogram_Phase_1_Info) is
   begin
      Write_Line ("Subprogram " & Info.Subprogram.all);

      Write_Line ("Proof_Ins:");
      for Name of Info.Inputs_Proof loop
         Write_Line ("   " & Name.all);
      end loop;

      Write_Line ("Inputs:");
      for Name of Info.Inputs loop
         Write_Line ("   " & Name.all);
      end loop;

      Write_Line ("Outputs:");
      for Name of Info.Outputs loop
         Write_Line ("   " & Name.all);
      end loop;

      Write_Line ("Proof calls:");
      for Name of Info.Proof_Calls loop
         Write_Line ("   " & Name.all);
      end loop;

      Write_Line ("Definite calls:");
      for Name of Info.Definite_Calls loop
         Write_Line ("   " & Name.all);
      end loop;

      Write_Line ("Conditional calls:");
      for Name of Info.Conditional_Calls loop
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

      Current_Mode := GG_Write_Mode;
   end GG_Write_Initialize;

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
      Conditional_Calls : Node_Sets.Set)
   is
      function To_Name (E : Entity_Id) return Entity_Name;
      function To_Name_Set (S : Node_Sets.Set) return Name_Set.Set;

      function To_Name (E : Entity_Id) return Entity_Name
      is (new String'(Unique_Name (E)));

      function To_Name_Set (S : Node_Sets.Set) return Name_Set.Set
      is
         Rv : Name_Set.Set := Name_Set.Empty_Set;
      begin
         for E of S loop
            Rv.Insert (To_Name (E));
         end loop;
         return Rv;
      end To_Name_Set;
   begin
      Info_Set.Insert ((To_Name (E),
                        Inputs_Proof      => To_Name_Set (Inputs_Proof),
                        Inputs            => To_Name_Set (Inputs),
                        Outputs           => To_Name_Set (Outputs),
                        Proof_Calls       => To_Name_Set (Proof_Calls),
                        Definite_Calls    => To_Name_Set (Definite_Calls),
                        Conditional_Calls => To_Name_Set (Conditional_Calls)));
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
      end loop;

      Close_Output_Library_Info;
      Current_Mode := GG_No_Mode;
   end GG_Write_Finalize;

   -------------
   -- GG_Read --
   -------------

   procedure GG_Read (GNAT_Root : Node_Id) is
      All_Globals     : Name_Set.Set := Name_Set.Empty_Set;
      --  Contains all global variables

      All_Subprograms : Name_Set.Set := Name_Set.Empty_Set;
      --  Contains all subprograms

      procedure Add_All_Edges;
      --  Reads the populated Info_Set and generates all the edges of
      --  the Global_Graph.

      procedure Add_Edge (G1, G2 : Global_Id);
      --  Adds an edge between the vertices V1 and V2 that correspond
      --  to G1 and G2 (V1 --> V2). The edge has the default color.

      procedure Create_All_Vertices;
      --  Creates all the vertices of the Global_Graph.

      procedure Load_GG_Info_From_ALI (ALI_File_Name : File_Name_Type);
      --  Gets the GG info from an ALI file and stores them in the
      --  Info_Set table.
      --
      --  The info that we read look as follows:
      --
      --  GG S test__proc
      --  GG VP test__proof_var
      --  GG VI test__g test__g2
      --  GG VO test__g
      --  GG CP test__ghost_func_a test__ghost_func_b
      --  GG CD test__proc_2
      --  GG CC test__proc_3

      -------------------
      -- Add_All_Edges --
      -------------------

      procedure Add_All_Edges is
         G_Ins, G_Outs, G_Proof_Ins : Global_Id;
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

         --  Close graph
         declare
            procedure Dummy_Proc (A, B : Global_Graphs.Vertex_Id);
            --  Dummy procedure that does nothing. Will be used when we
            --  transitively close the graph.

            ----------------
            -- Dummy_Proc --
            ----------------

            procedure Dummy_Proc (A, B : Global_Graphs.Vertex_Id) is
               pragma Unreferenced (A, B);
            begin
               null;
            end Dummy_Proc;
         begin
            Global_Graphs.Close (G       => Global_Graph,
                                 Visitor => Dummy_Proc'Access);
         end;
      end Add_All_Edges;

      --------------
      -- Add_Edge --
      --------------

      procedure Add_Edge (G1, G2 : Global_Id) is
      begin
         Global_Graph.Add_Edge (Global_Graph.Get_Vertex (G1),
                                Global_Graph.Get_Vertex (G2),
                                EC_Default);
      end Add_Edge;

      -------------------------
      -- Create_All_Vertices --
      -------------------------

      procedure Create_All_Vertices is
      begin
         --  Create vertices for all global variables
         for N of All_Globals loop
            declare
               G : constant Global_Id := Global_Id'(Kind => Variable_Kind,
                                                    Name => N);
               V : Global_Graphs.Vertex_Id;
            begin
               Global_Graph.Add_Vertex (G, V);
            end;
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

               V_Ins, V_Outs, V_Proof_Ins : Global_Graphs.Vertex_Id;
            begin
               Global_Graph.Add_Vertex (G_Ins, V_Ins);
               Global_Graph.Add_Vertex (G_Outs, V_Outs);
               Global_Graph.Add_Vertex (G_Proof_Ins, V_Proof_Ins);
            end;
         end loop;
      end Create_All_Vertices;

      ---------------------------
      -- Load_GG_Info_From_ALI --
      ---------------------------

      procedure Load_GG_Info_From_ALI (ALI_File_Name : File_Name_Type) is
         ALI_File_Name_Str : constant String :=
           Name_String (Name_Id (Full_Lib_File_Name (ALI_File_Name)));

         ALI_File : Ada.Text_IO.File_Type;
         Line     : Unbounded_String;
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

         --  We have now reached the GG section of the ALI file
         while not End_Of_File (ALI_File) loop
            declare
               New_Info : Subprogram_Phase_1_Info;

               type Variable_Or_Subprogram is (Var, Sub);

               procedure Parse_Line (Var_Or_Sub : Variable_Or_Subprogram;
                                     NS         : out Name_Set.Set);
               --  Returns a Name_Set (NS) with every Entity_Name
               --  contained in Line. If Var_Or_Sub is set to Variable
               --  it then we add the Entity_Ids that correspond to
               --  the Entity_Names of NS to the All_Globals set. If
               --  Var_Or_Sub is set to Sub then we add the Entity_ids
               --  that correspond to NS to the All_Subprograms set.

               ---------------
               -- Parse_Line --
               ---------------

               procedure Parse_Line (Var_Or_Sub : Variable_Or_Subprogram;
                                     NS         : out Name_Set.Set)
               is
                  Names_In_Line : Name_Set.Set := Name_Set.Empty_Set;
                  Start_Of_Word : Natural      := 7;
                  End_Of_Word   : Natural;
               begin
                  if Length (Line) <= 5 then
                     --  This line is of the form "GG **". Nothing to
                     --  read here. We set NS to Name_Set.Empty_Set
                     --  and return.
                     NS := Names_In_Line;
                     return;
                  end if;

                  while Start_Of_Word < Length (Line) loop
                     End_Of_Word := Start_Of_Word;

                     while End_Of_Word < Length (Line)
                       and then Element (Line, End_Of_Word) > ' '
                     loop
                        End_Of_Word := End_Of_Word + 1;
                     end loop;

                     --  If we have not reached the end of the line
                     --  then we have read one character too many.
                     if End_Of_Word < Length (Line) then
                        End_Of_Word := End_Of_Word - 1;
                     end if;

                     declare
                        EN : constant Entity_Name :=
                          new String'(Slice (Line,
                                             Start_Of_Word,
                                             End_Of_Word));
                     begin
                        Names_In_Line.Include (EN);

                        if Var_Or_Sub = Var then
                           --  Add variable to the set of All_Globals
                           All_Globals.Include (EN);
                        else
                           --  Add subprogram to the set of
                           --  All_Subprograms.
                           All_Subprograms.Include (EN);
                        end if;
                     end;

                     Start_Of_Word := End_Of_Word + 2;
                  end loop;

                  NS := Names_In_Line;
               end Parse_Line;
            begin
               --  Read subprogram and add it to the set of
               --  All_Subprograms.
               declare
                  EN : constant Entity_Name :=
                    new String'(Slice (Line,
                                       6,
                                       Length (Line)));
               begin
                  New_Info.Subprogram := EN;
                  All_Subprograms.Include (EN);
               end;

               --  Read Inputs_Proof
               Get_Line (ALI_File, Line);
               Parse_Line (Var, New_Info.Inputs_Proof);

               --  Read Inputs
               Get_Line (ALI_File, Line);
               Parse_Line (Var, New_Info.Inputs);

               --  Read Outputs
               Get_Line (ALI_File, Line);
               Parse_Line (Var, New_Info.Outputs);

               --  Read Proof_Calls
               Get_Line (ALI_File, Line);
               Parse_Line (Sub, New_Info.Proof_Calls);

               --  Read Definite_Calls
               Get_Line (ALI_File, Line);
               Parse_Line (Sub, New_Info.Definite_Calls);

               --  Read Conditional_Calls
               Get_Line (ALI_File, Line);
               Parse_Line (Sub, New_Info.Conditional_Calls);

               --  Add the record on the Info_Set
               Info_Set.Include (New_Info);
            end;

            if not End_Of_File (ALI_File) then
               --  Moving on to the next subprogram
               Get_Line (ALI_File, Line);
            end if;
         end loop;

         Close (ALI_File);
      end Load_GG_Info_From_ALI;

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
      end if;

      --  Initialize Global_Graph
      Global_Graph := Global_Graphs.Create;

      --  Create all vertices of the Global_Graph
      Create_All_Vertices;

      --  Add all edges in the Global_Graph
      Add_All_Edges;

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

   function GG_Exist (E : Entity_Id) return Boolean
   is
      pragma Unreferenced (E);
   begin
      return False;
   end GG_Exist;

   --------------------
   -- GG_Get_Globals --
   --------------------

   procedure GG_Get_Globals (E           : Entity_Id;
                             Proof_Reads : out Flow_Id_Sets.Set;
                             Reads       : out Flow_Id_Sets.Set;
                             Writes      : out Flow_Id_Sets.Set)
   is
      pragma Unreferenced (E);
   begin
      Proof_Reads := Flow_Id_Sets.Empty_Set;
      Reads       := Flow_Id_Sets.Empty_Set;
      Writes      := Flow_Id_Sets.Empty_Set;
   end GG_Get_Globals;

   ------------------------
   -- GG_Get_Proof_Reads --
   ------------------------

   function GG_Get_Proof_Reads (E : Entity_Id) return Flow_Id_Sets.Set
   is
      pragma Unreferenced (E);
   begin
      return Flow_Id_Sets.Empty_Set;
   end GG_Get_Proof_Reads;

   ------------------
   -- GG_Get_Reads --
   ------------------

   function GG_Get_Reads (E : Entity_Id) return Flow_Id_Sets.Set
   is
      pragma Unreferenced (E);
   begin
      return Flow_Id_Sets.Empty_Set;
   end GG_Get_Reads;

   ----------------------
   -- GG_Get_All_Reads --
   ----------------------

   function GG_Get_All_Reads (E : Entity_Id) return Flow_Id_Sets.Set
   is
   begin
      return GG_Get_Proof_Reads (E) or GG_Get_Reads (E);
   end GG_Get_All_Reads;

   -------------------
   -- GG_Get_Writes --
   -------------------

   function GG_Get_Writes (E : Entity_Id) return Flow_Id_Sets.Set
   is
      pragma Unreferenced (E);
   begin
      return Flow_Id_Sets.Empty_Set;
   end GG_Get_Writes;

end Flow_Computed_Globals;
