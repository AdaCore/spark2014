------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                        F L O W . A N A L Y S I S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2013, Altran UK Limited                   --
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

with Ada.Characters.Handling; use Ada.Characters.Handling;
with Ada.Strings.Maps;        use Ada.Strings.Maps;
with Ada.Strings.Unbounded;   use Ada.Strings.Unbounded;
with Ada.Text_IO;

with Aspects;               use Aspects;
with Errout;                use Errout;
with Namet;                 use Namet;
with Nlists;                use Nlists;
with Sinput;                use Sinput;
with Sem_Util;              use Sem_Util;
with Snames;                use Snames;

with Treepr;                use Treepr;

with Why;

with Flow.Slice;            use Flow.Slice;
with Flow.Utility;          use Flow.Utility;

package body Flow.Analysis is

   use type Ada.Containers.Count_Type;
   use type Flow_Graphs.Vertex_Id;
   use type Node_Sets.Set;
   use type Flow_Id_Sets.Set;

   function Error_Location (G : Flow_Graphs.T'Class;
                            V : Flow_Graphs.Vertex_Id)
                            return Node_Or_Entity_Id;
   --  Find a good place to raise an error for vertex V.

   function Substitute (S : Unbounded_String;
                        F : Flow_Id)
                        return Unbounded_String;
   --  Find the first '&' and substitute with the given flow id.

   function Create_Tag (Tag : String;
                        F1  : Flow_Id := Null_Flow_Id;
                        F2  : Flow_Id := Null_Flow_Id)
                        return String;
   --  Produce a tag for use in error messages. If flow ids are
   --  provided they are included in the tag. For example:
   --     Create_Tag ("foo")     ->   "foo"
   --     Create_Tag ("foo", a)  ->   "foo__r_discriminant"

   procedure Error_Msg_Flow (Msg : String;
                             G   : Flow_Graphs.T'Class;
                             Loc : Flow_Graphs.Vertex_Id;
                             Tag : String := "");
   --  Output an error message attaced to the given vertex.

   procedure Error_Msg_Flow (Msg : String;
                             G   : Flow_Graphs.T'Class;
                             Loc : Flow_Graphs.Vertex_Id;
                             F   : Flow_Id;
                             Tag : String := "");
   --  Output an error message attaced to the given vertex with a
   --  substitution using F. Use & as the substitution character.

   procedure Error_Msg_Flow (Msg : String;
                             N   : Node_Id;
                             F1  : Flow_Id;
                             Tag : String := "");
   --  Output an error message attaced to the given node with a
   --  substitution using F1. Use & as the substitution character.

   procedure Error_Msg_Flow (Msg : String;
                             N   : Node_Id;
                             F1  : Flow_Id;
                             F2  : Flow_Id;
                             Tag : String := "");
   --  As above with two nodes to substitute.

   function Get_Line (G   : Flow_Graphs.T'Class;
                      V   : Flow_Graphs.Vertex_Id;
                      Sep : Character := ':')
                     return String;
   --  Obtain the location for the given vertex as in "foo.adb:12".

   procedure Write_Vertex_Set
     (G     : Flow_Graphs.T;
      E_Loc : Node_Or_Entity_Id;
      Set   : Vertex_Sets.Set;
      Tag   : String);
   --  Write a trace file for GPS.

   procedure Global_Required
     (FA  : Flow_Analysis_Graphs;
      Var : Flow_Id)
      with Pre => Var.Kind = Magic_String;
   --  Emit an error message that (the first call) introducing the
   --  global Var requires a global annotation.

   function Find_Global (S : Entity_Id;
                         F : Flow_Id)
                         return Node_Id;
   --  Find the given global F in the subprogram declaration of S. If
   --  we can't find it (perhaps because of computed globals) we just
   --  return S which is a useful fallback place to raise an error.

   --------------------
   -- Error_Location --
   --------------------

   function Error_Location (G : Flow_Graphs.T'Class;
                            V : Flow_Graphs.Vertex_Id)
                            return Node_Or_Entity_Id
   is
      K : constant Flow_Id      := G.Get_Key (V);
      A : constant V_Attributes := G.Get_Attributes (V);
   begin
      if Present (A.Error_Location) then
         return A.Error_Location;

      else
         case K.Kind is
            when Direct_Mapping | Record_Field =>
               return Get_Direct_Mapping_Id (K);

            when others =>
               raise Why.Unexpected_Node;
         end case;
      end if;
   end Error_Location;

   ----------------
   -- Substitute --
   ----------------

   function Substitute (S : Unbounded_String;
                        F : Flow_Id)
                        return Unbounded_String
   is
      R      : Unbounded_String := Null_Unbounded_String;
      Do_Sub : Boolean          := True;
   begin
      for Index in Positive range 1 .. Length (S) loop
         if Do_Sub and then Element (S, Index) = '&' then
            case  F.Kind is
               when Null_Value =>
                  Append (R, "NULL");

               when Direct_Mapping | Record_Field =>
                  Append (R, """");
                  Append (R, Flow_Id_To_String (F));
                  Append (R, """");

               when Magic_String =>
                  --  ??? we may want to use __gnat_decode() here instead
                  Append (R, """");
                  declare
                     Index : Positive := 1;
                  begin
                     --  Replace __ with . in the magic string.
                     while Index <= F.Name.all'Length loop
                        case F.Name.all (Index) is
                           when '_' =>
                              if Index < F.Name.all'Length and then
                                F.Name.all (Index) = '_' then
                                 Append (R, ".");
                                 Index := Index + 2;
                              else
                                 Append (R, '_');
                                 Index := Index + 1;
                              end if;

                           when others =>
                              Append (R, F.Name.all (Index));
                              Index := Index + 1;
                        end case;
                     end loop;
                  end;
                  Append (R, """");

            end case;
            Do_Sub := False;

         else
            Append (R, Element (S, Index));
         end if;
      end loop;
      return R;
   end Substitute;

   ----------------
   -- Create_Tag --
   ----------------

   function Create_Tag (Tag : String;
                        F1  : Flow_Id := Null_Flow_Id;
                        F2  : Flow_Id := Null_Flow_Id)
                        return String
   is
      R : Unbounded_String := Null_Unbounded_String;
   begin
      if Tag'Length = 0 then
         return To_String (R);
      end if;

      Append (R, Tag);

      if F1 /= Null_Flow_Id then
         Append (R, "__");
         Append (R, Flow_Id_To_String (F1));
      end if;

      if F2 /= Null_Flow_Id then
         Append (R, "__");
         Append (R, Flow_Id_To_String (F2));
      end if;

      Translate (R, To_Mapping (".", "_"));

      return To_Lower (To_String (R));
   end Create_Tag;

   --------------------
   -- Error_Msg_Flow --
   --------------------

   procedure Error_Msg_Flow (Msg : String;
                             G   : Flow_Graphs.T'Class;
                             Loc : Flow_Graphs.Vertex_Id;
                             Tag : String := "") is
   begin
      if Tag'Length >= 1 then
         Error_Msg_N (Msg & " [" & Tag & "]!", Error_Location (G, Loc));
      else
         Error_Msg_N (Msg & "!", Error_Location (G, Loc));
      end if;
   end Error_Msg_Flow;

   procedure Error_Msg_Flow (Msg : String;
                             N   : Node_Id;
                             F1  : Flow_Id;
                             Tag : String := "")
   is
      M : Unbounded_String;
   begin

      --  Assemble message string to be passed to Error_Msg_N
      M := Substitute (To_Unbounded_String (Msg),
                       F1);
      if Tag'Length >= 1 then
         Append (M, " [" & Tag & "]");
      end if;
      Append (M, '!');

      --  Issue error message
      Error_Msg_N (To_String (M), N);

   end Error_Msg_Flow;

   procedure Error_Msg_Flow (Msg : String;
                             N   : Node_Id;
                             F1  : Flow_Id;
                             F2  : Flow_Id;
                             Tag : String := "")
   is
      M : Unbounded_String;
   begin

      --  Assemble message string to be passed to Error_Msg_N
      M := Substitute (Substitute (To_Unbounded_String (Msg),
                                   F1),
                       F2);
      if Tag'Length >= 1 then
         Append (M, " [" & Tag & "]");
      end if;
      Append (M, '!');

      --  Issue error message
      Error_Msg_N (To_String (M), N);

   end Error_Msg_Flow;

   procedure Error_Msg_Flow (Msg : String;
                             G   : Flow_Graphs.T'Class;
                             Loc : Flow_Graphs.Vertex_Id;
                             F   : Flow_Id;
                             Tag : String := "")
   is
      L : constant Node_Or_Entity_Id := Error_Location (G, Loc);
   begin
      Error_Msg_Flow (Msg => Msg,
                      N   => L,
                      F1  => F,
                      Tag => Tag);
   end Error_Msg_Flow;

   --------------
   -- Get_Line --
   --------------

   function Get_Line (G   : Flow_Graphs.T'Class;
                      V   : Flow_Graphs.Vertex_Id;
                      Sep : Character := ':')
                      return String
   is
      N       : constant Node_Or_Entity_Id := Error_Location (G, V);
      SI      : constant Source_File_Index := Get_Source_File_Index (Sloc (N));
      Line_No : constant String :=
        Logical_Line_Number'Image (Get_Logical_Line_Number (Sloc (N)));
   begin
      return Get_Name_String (File_Name (SI)) & Sep &
        Line_No (2 .. Line_No'Last);
   end Get_Line;

   ----------------------
   -- Write_Vertex_Set --
   ----------------------

   procedure Write_Vertex_Set
     (G     : Flow_Graphs.T;
      E_Loc : Node_Or_Entity_Id;
      Set   : Vertex_Sets.Set;
      Tag   : String)
   is
      SI      : constant Source_File_Index :=
        Get_Source_File_Index (Sloc (E_Loc));

      Line_No : constant String :=
        Logical_Line_Number'Image (Get_Logical_Line_Number (Sloc (E_Loc)));

      Col_No  : constant String :=
        Column_Number'Image (Get_Column_Number (Sloc (E_Loc)));

      Filename : constant String :=
        Get_Name_String (File_Name (SI)) &
        "_" & Line_No (2 .. Line_No'Last) &
        "_" & Col_No (2 .. Col_No'Last) &
        "_" & Tag &
        ".trace";

      FD       : Ada.Text_IO.File_Type;
   begin
      Ada.Text_IO.Create (FD, Ada.Text_IO.Out_File, Filename);

      for V of Set loop
         declare
            F : constant Flow_Id := G.Get_Key (V);
         begin
            if F.Kind = Direct_Mapping then
               Ada.Text_IO.Put (FD, Get_Line (G, V));
               Ada.Text_IO.New_Line (FD);
            end if;
         end;
      end loop;

      Ada.Text_IO.Close (FD);
   end Write_Vertex_Set;

   ---------------------
   -- Global_Required --
   ---------------------

   procedure Global_Required
     (FA  : Flow_Analysis_Graphs;
      Var : Flow_Id)
   is
      Offending_Subprograms : constant Node_Sets.Set :=
        FA.Magic_Source (Var.Name);

      Error_Issued : Boolean := False;

      function Find_First_Call_With_Global (F : Flow_Id) return Node_Id;
      --  Find the first statement which defines or depends on Var.

      function Proc_Issue_Errors (N : Node_Id) return Traverse_Result;
      --  Issue errors on each offending subprogram call.

      function Find_First_Call_With_Global (F : Flow_Id) return Node_Id is
         RV    : Node_Id;
         Found : Boolean := False;

         procedure Are_We_There_Yet
           (V      : Flow_Graphs.Vertex_Id;
            Origin : Flow_Graphs.Vertex_Id;
            Depth  : Natural;
            T_Ins  : out Flow_Graphs.Simple_Traversal_Instruction);
         --  Check if we have found a call with F as a global.

         procedure Are_We_There_Yet
           (V      : Flow_Graphs.Vertex_Id;
            Origin : Flow_Graphs.Vertex_Id;
            Depth  : Natural;
            T_Ins  : out Flow_Graphs.Simple_Traversal_Instruction)
         is
            pragma Unreferenced (Depth, Origin);

            A : constant V_Attributes := FA.CFG.Get_Attributes (V);
         begin
            if A.Is_Global_Parameter and then
              Change_Variant (F, Normal_Use) =
              Change_Variant (A.Parameter_Formal, Normal_Use)
            then
               --  We have found a procedure call where F is a global.
               T_Ins := Flow_Graphs.Abort_Traversal;
               RV    := Get_Direct_Mapping_Id (A.Call_Vertex);
               Found := True;

            elsif A.Variables_Used.Contains
              (Change_Variant (F, Normal_Use))
            then
               --  We have found an expression which directly depends
               --  on the global.
               T_Ins := Flow_Graphs.Abort_Traversal;
               RV    := Get_Direct_Mapping_Id (FA.CFG.Get_Key (V));
               Found := True;

            else
               T_Ins := Flow_Graphs.Continue;
            end if;
         end Are_We_There_Yet;

      begin
         FA.CFG.BFS (Start         => FA.Start_Vertex,
                     Include_Start => False,
                     Visitor       => Are_We_There_Yet'Access);
         pragma Assert (Found);
         return RV;
      end Find_First_Call_With_Global;

      function Proc_Issue_Errors (N : Node_Id) return Traverse_Result is
      begin
         case Nkind (N) is
            when N_Procedure_Call_Statement | N_Function_Call =>
               if Offending_Subprograms.Contains (Entity (Name (N))) then
                  Error_Msg_NE
                    ("called subprogram & requires GLOBAL aspect" &
                       " to make state visible",
                     N,
                     Entity (Name (N)));
                  Error_Issued := True;
               end if;

            when others =>
               null;
         end case;
         return OK;
      end Proc_Issue_Errors;

      procedure Traverse is new Traverse_Proc (Process => Proc_Issue_Errors);

   begin
      Traverse (Find_First_Call_With_Global (Var));
      pragma Assert (Error_Issued);
   end Global_Required;

   -----------------
   -- Find_Global --
   -----------------

   function Find_Global (S : Entity_Id;
                         F : Flow_Id)
                         return Node_Id
   is
      Needle     : Entity_Id;
      Haystack   : Node_Id;
      The_Global : Node_Id := Empty;

      function Find_It (N : Node_Id) return Traverse_Result;
      --  Checks if N refers to Needle and sets The_Global to N if
      --  that is the case.

      function Find_It (N : Node_Id) return Traverse_Result is
      begin
         case Nkind (N) is
            when N_Identifier | N_Expanded_Name =>
               if Present (Entity (N)) and then
                 Nkind (Entity (N)) in N_Entity and then  -- !!! workaround
                 Unique_Entity (Entity (N)) = Needle
               then
                  The_Global := N;
                  return Abandon;
               else
                  return OK;
               end if;
            when others =>
               return OK;
         end case;
      end Find_It;

      procedure Look_For_Global is new Traverse_Proc (Find_It);
   begin
      if Workaround_Pre_30_Apr_2013 then
         Haystack := Find_Aspect (S, Aspect_Global);
      else
         --  Get_Pragma only works reliably in recent front-end
         --  versions.
         Haystack := Get_Pragma (S, Pragma_Global);
      end if;

      case F.Kind is
         when Direct_Mapping | Record_Field =>
            Needle := Get_Direct_Mapping_Id (F);
            Look_For_Global (Haystack);
            if Present (The_Global) then
               return The_Global;
            else
               return S;
            end if;

         when Magic_String =>
            return S;

         when Null_Value =>
            raise Why.Unexpected_Node;
      end case;
   end Find_Global;

   ------------------
   -- Sanity_Check --
   ------------------

   procedure Sanity_Check (FA   : Flow_Analysis_Graphs;
                           Sane : out Boolean)
   is
   begin
      --  Innocent until proven guilty.
      Sane := True;

      --  Sanity check all vertices if they mention a flow id that we
      --  do not know about.

      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            A : constant V_Attributes := FA.CFG.Get_Attributes (V);

            All_Vars : constant Ordered_Flow_Id_Sets.Set :=
              To_Ordered_Flow_Id_Set (A.Variables_Used or A.Variables_Defined);
         begin
            for Var of All_Vars loop
               declare
                  Neutral : constant Flow_Id :=
                    Change_Variant (Var, Normal_Use);
               begin
                  if not FA.All_Vars.Contains (Neutral) then
                     case Neutral.Kind is
                        when Direct_Mapping =>
                           Error_Msg_Flow
                             (Msg => "& must be listed in the Global aspect",
                              G   => FA.CFG,
                              Loc => V,
                              F   => Var);

                        when Magic_String =>
                           Global_Required (FA, Var);

                        when others =>
                           raise Why.Unexpected_Node;
                     end case;
                     Sane := False;
                  end if;
               end;
            end loop;
         end;
      end loop;

      if not Sane then
         Error_Msg_NE
           ("flow analysis of & abandoned due to inconsistent graph",
            FA.Subprogram,
            FA.Subprogram);
         return;
      end if;

      --  Sanity check for aliasing.

      pragma Assert (Sane);

      if FA.Aliasing_Present then
         Error_Msg_NE
           ("flow analysis of & abandoned due to aliasing",
            FA.Subprogram,
            FA.Subprogram);
         Sane := False;
         return;
      end if;

   end Sanity_Check;

   ------------------------------
   -- Find_Ineffective_Imports --
   ------------------------------

   procedure Find_Ineffective_Imports (FA : Flow_Analysis_Graphs)
   is
      function Is_Final_Use (V : Flow_Graphs.Vertex_Id) return Boolean
      is (FA.PDG.Get_Key (V).Variant = Final_Value and then
            FA.PDG.Get_Attributes (V).Is_Export);
      --  Checks if the given vertex V is a final-use vertex.

      Effective_Ids   : Vertex_Sets.Set := Vertex_Sets.Empty_Set;
      Entire_Ids      : Vertex_Sets.Set := Vertex_Sets.Empty_Set;

   begin
      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Key : constant Flow_Id      := FA.PDG.Get_Key (V);
            Atr : constant V_Attributes := FA.PDG.Get_Attributes (V);
         begin
            if Key.Variant = Initial_Value
              and then Atr.Is_Initialised
              and then (not Atr.Is_Loop_Parameter)
            then
               --  Note the entire variable.
               declare
                  P : Flow_Graphs.Vertex_Id := V;
               begin
                  while P /= Flow_Graphs.Null_Vertex loop
                     if FA.CFG.Parent (P) = Flow_Graphs.Null_Vertex then
                        Entire_Ids.Include (P);
                        exit;
                     end if;
                     P := FA.CFG.Parent (P);
                  end loop;
               end;

               --  Check if we're ineffective or not.
               if FA.PDG.Non_Trivial_Path_Exists (V,
                                                  Is_Final_Use'Access)
               then
                  --  We can reach a final use vertex, so we are doing
                  --  something useful. We flag up the entire chain as
                  --  being useful.
                  Effective_Ids.Include (V);
                  declare
                     P : Flow_Graphs.Vertex_Id := V;
                  begin
                     while P /= Flow_Graphs.Null_Vertex loop
                        Effective_Ids.Include (P);
                        P := FA.CFG.Parent (P);
                     end loop;
                  end;
               else
                  --  We cannot reach any final use vertex, hence the
                  --  import of V is ineffective.
                  null;
               end if;
            end if;
         end;
      end loop;

      --  Now that we can issue error messages. We can't do it inline
      --  because we need to pay special attention to records.
      for V of Entire_Ids loop
         if not Effective_Ids.Contains (V) then
            declare
               F : constant Flow_Id      := FA.PDG.Get_Key (V);
               A : constant V_Attributes := FA.PDG.Get_Attributes (V);
            begin
               if Is_Discriminant (F) then
                  --  Discriminants are never ineffective imports.
                  null;
               elsif A.Is_Global then
                  Error_Msg_Flow (Msg => "ineffective global import &",
                                  N   => Find_Global (FA.Subprogram, F),
                                  F1  => F);
               else
                  Error_Msg_Flow (Msg => "ineffective import &",
                                  G   => FA.PDG,  --  !!! find_import
                                  Loc => V,
                                  F   => F);
               end if;
            end;
         end if;
      end loop;
   end Find_Ineffective_Imports;

   --------------------------
   -- Find_Illegal_Updates --
   --------------------------

   procedure Find_Illegal_Updates (FA : Flow_Analysis_Graphs) is
      procedure Print_Error (Illegal_Use_Loc : Flow_Graphs.Vertex_Id;
                             The_Global_Id   : Flow_Id;
                             The_Global_Atr  : V_Attributes);
      --  Helper procedure to print the error message.

      procedure Print_Error (Illegal_Use_Loc : Flow_Graphs.Vertex_Id;
                             The_Global_Id   : Flow_Id;
                             The_Global_Atr  : V_Attributes)
      is
         Illegal_Use_Atr : constant V_Attributes :=
           FA.PDG.Get_Attributes (Illegal_Use_Loc);
      begin
         if The_Global_Atr.Is_Global then
            if Illegal_Use_Atr.Is_Parameter then
               --  foo (bar);
               Error_Msg_Flow
                 (Msg => "actual for & cannot be a global input",
                  G   => FA.PDG,
                  Loc => Illegal_Use_Loc,
                  F   => Illegal_Use_Atr.Parameter_Formal);

            elsif Illegal_Use_Atr.Is_Global_Parameter then
               --  foo;
               Error_Msg_Flow
                 (Msg => "global item & must denote a global output",
                  G   => FA.PDG,
                  Loc => Illegal_Use_Loc,
                  F   => The_Global_Id);

            else
               --  bar := 12;
               Error_Msg_Flow
                 (Msg => "assignment to global in & not allowed",
                  G   => FA.PDG,
                  Loc => Illegal_Use_Loc,
                  F   => The_Global_Id);
            end if;
         else
            --  It *has* to be a global. The compiler would catch any
            --  updates to in parameters and loop parameters...
            raise Why.Unexpected_Node;
         end if;
      end Print_Error;
   begin
      --  We look at all vertices...
      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         --  For any vertex which defines a variable (at most one, I
         --  suppose) we check we are allowed to define that variable.
         for Var of FA.PDG.Get_Attributes (V).Variables_Defined loop
            declare
               Corresp_Final_Vertex : constant Flow_Graphs.Vertex_Id :=
                 FA.PDG.Get_Vertex (Change_Variant (Var, Final_Value));
               pragma Assert (Corresp_Final_Vertex /=
                                Flow_Graphs.Null_Vertex);

               Final_Atr : constant V_Attributes :=
                 FA.PDG.Get_Attributes (Corresp_Final_Vertex);
            begin
               --  We only do this check if Var is something which we
               --  should not change.
               if Final_Atr.Is_Constant and not
                 Final_Atr.Is_Loop_Parameter then
                  if FA.PDG.Get_Key (V).Variant = Initial_Value then
                     --  The initial use vertex is, of course, allowed
                     --  to define the variable.
                     null;
                  else
                     Print_Error (Illegal_Use_Loc => V,
                                  The_Global_Id   => Var,
                                  The_Global_Atr  => Final_Atr);
                  end if;
               end if;
            end;
         end loop;
      end loop;
   end Find_Illegal_Updates;

   ---------------------------------
   -- Find_Ineffective_Statements --
   ---------------------------------

   procedure Find_Ineffective_Statements (FA : Flow_Analysis_Graphs) is
      function Is_Final_Use (V : Flow_Graphs.Vertex_Id) return Boolean;
      --  Checks if the given vertex V is a final-use vertex.

      function Find_Masking_Code
        (Ineffective_Statement : Flow_Graphs.Vertex_Id)
         return Vertex_Sets.Set;
      --  Find out why a given vertex is ineffective. A vertex is
      --  ineffective if the variable(s) defined by it are re-defined
      --  on all paths leading from it without being used. Thus all
      --  reachable vertices which also define at least one variable
      --  of that set (and do not use it), render the vertex
      --  ineffective.

      function Is_Final_Use (V : Flow_Graphs.Vertex_Id) return Boolean is
      begin
         return FA.PDG.Get_Key (V).Variant = Final_Value and then
           FA.PDG.Get_Attributes (V).Is_Export;
      end Is_Final_Use;

      function Find_Masking_Code
        (Ineffective_Statement : Flow_Graphs.Vertex_Id)
         return Vertex_Sets.Set
      is
         Mask         : Vertex_Sets.Set := Vertex_Sets.Empty_Set;
         Vars_Defined : constant Flow_Id_Sets.Set :=
           FA.CFG.Get_Attributes (Ineffective_Statement).Variables_Defined;

         procedure Visitor
           (V  : Flow_Graphs.Vertex_Id;
            TV : out Flow_Graphs.Simple_Traversal_Instruction);
         --  Check if V masks the ineffective statement.

         procedure Visitor
           (V  : Flow_Graphs.Vertex_Id;
            TV : out Flow_Graphs.Simple_Traversal_Instruction)
         is
            Intersection : constant Flow_Id_Sets.Set :=
              Vars_Defined and
              (FA.CFG.Get_Attributes (V).Variables_Defined -
                 FA.CFG.Get_Attributes (V).Variables_Used);
         begin
            if V /= Ineffective_Statement and then
              Intersection.Length >= 1
            then
               Mask.Include (V);
               TV := Flow_Graphs.Skip_Children;
            else
               TV := Flow_Graphs.Continue;
            end if;
         end Visitor;

      begin
         FA.CFG.DFS (Start         => Ineffective_Statement,
                     Include_Start => False,
                     Visitor       => Visitor'Access);
         return Mask;
      end Find_Masking_Code;

   begin
      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Atr  : constant V_Attributes := FA.PDG.Get_Attributes (V);
            Mask : Vertex_Sets.Set;
         begin
            if Atr.Is_Program_Node then
               if not FA.PDG.Non_Trivial_Path_Exists
                 (V, Is_Final_Use'Access)
               then
                  Mask := Find_Masking_Code (V);

                  if Mask.Length >= 1 then
                     --  We have a useful path we can show.
                     Error_Msg_Flow
                       (Msg => "ineffective statement",
                        G   => FA.PDG,
                        Loc => V,
                        Tag => Create_Tag ("ineffective"));
                     Write_Vertex_Set
                       (G     => FA.PDG,
                        E_Loc => Error_Location (FA.PDG, V),
                        Set   => Mask,
                        Tag   => Create_Tag ("ineffective"));

                  else
                     --  The variables defined by this statement are
                     --  just not used; no useful path can be show.
                     Error_Msg_Flow (Msg => "ineffective statement",
                                     G   => FA.PDG,
                                     Loc => V);
                  end if;
               end if;
            end if;
         end;
      end loop;
   end Find_Ineffective_Statements;

   -----------------------------------------
   -- Find_Use_Of_Uninitialised_Variables --
   -----------------------------------------

   procedure Find_Use_Of_Uninitialised_Variables
     (FA : Flow_Analysis_Graphs)
   is
      procedure Mark_Definition_Free_Path
        (E_Loc : Flow_Graphs.Vertex_Id;
         From  : Flow_Graphs.Vertex_Id;
         To    : Flow_Graphs.Vertex_Id;
         Var   : Flow_Id;
         Tag   : String);
      --  Write a trace file for the error message at E_Loc with the
      --  given Tag. The trace will mark the path From -> To which
      --  does not define Var.

      procedure Mark_Definition_Free_Path
        (E_Loc : Node_Id;
         From  : Flow_Graphs.Vertex_Id;
         To    : Flow_Graphs.Vertex_Id;
         Var   : Flow_Id;
         Tag   : String);
      --  As above but allows a node to specify where the trace is
      --  attached.

      -------------------------------
      -- Mark_Definition_Free_Path --
      -------------------------------

      procedure Mark_Definition_Free_Path
        (E_Loc : Node_Id;
         From  : Flow_Graphs.Vertex_Id;
         To    : Flow_Graphs.Vertex_Id;
         Var   : Flow_Id;
         Tag   : String)
      is
         Path_Found : Boolean := False;
         Path       : Vertex_Sets.Set;

         procedure Are_We_There_Yet
           (V           : Flow_Graphs.Vertex_Id;
            Instruction : out Flow_Graphs.Traversal_Instruction);
         --  Visitor procedure for Shortest_Path.

         procedure Add_Loc
           (V : Flow_Graphs.Vertex_Id);
         --  Step procedure for Shortest_Path.

         procedure Are_We_There_Yet
           (V           : Flow_Graphs.Vertex_Id;
            Instruction : out Flow_Graphs.Traversal_Instruction)
         is
            A : constant V_Attributes := FA.CFG.Get_Attributes (V);
         begin
            if V = To then
               Instruction := Flow_Graphs.Found_Destination;
               Path_Found  := True;
            elsif A.Variables_Defined.Contains (Var) then
               Instruction := Flow_Graphs.Skip_Children;
            else
               Instruction := Flow_Graphs.Continue;
            end if;
         end Are_We_There_Yet;

         procedure Add_Loc
           (V : Flow_Graphs.Vertex_Id)
         is
            F : constant Flow_Id := FA.CFG.Get_Key (V);
         begin
            if V /= To and F.Kind = Direct_Mapping then
               Path.Include (V);
            end if;
         end Add_Loc;

      begin
         FA.CFG.Shortest_Path (Start         => From,
                               Allow_Trivial => False,
                               Search        => Are_We_There_Yet'Access,
                               Step          => Add_Loc'Access);

         --  A little sanity check can't hurt.
         pragma Assert (Path_Found);

         Write_Vertex_Set (G     => FA.CFG,
                           E_Loc => E_Loc,
                           Set   => Path,
                           Tag   => Tag);
      end Mark_Definition_Free_Path;

      procedure Mark_Definition_Free_Path
        (E_Loc : Flow_Graphs.Vertex_Id;
         From  : Flow_Graphs.Vertex_Id;
         To    : Flow_Graphs.Vertex_Id;
         Var   : Flow_Id;
         Tag   : String)
      is
      begin
         Mark_Definition_Free_Path (E_Loc => Error_Location (FA.CFG, E_Loc),
                                    From  => From,
                                    To    => To,
                                    Var   => Var,
                                    Tag   => Tag);
      end Mark_Definition_Free_Path;

   begin
      for V_Initial of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Key_I : constant Flow_Id      := FA.PDG.Get_Key (V_Initial);
            Atr_I : constant V_Attributes := FA.PDG.Get_Attributes (V_Initial);
         begin
            if Key_I.Variant = Initial_Value and then
              not Atr_I.Is_Initialised then
               for V_Use of FA.PDG.Get_Collection
                 (V_Initial, Flow_Graphs.Out_Neighbours) loop
                  declare
                     Key_U : constant Flow_Id := FA.PDG.Get_Key (V_Use);
                     Atr_U : constant V_Attributes :=
                       FA.PDG.Get_Attributes (V_Use);
                  begin
                     if Key_U.Variant = Final_Value then
                        if Atr_U.Is_Global then
                           Error_Msg_Flow
                             (Msg => "global & might not be set",
                              N   => Find_Global (FA.Subprogram, Key_I),
                              F1  => Key_I,
                              Tag => Create_Tag ("uninitialized", Key_I));
                           Mark_Definition_Free_Path
                             (E_Loc => Find_Global (FA.Subprogram, Key_I),
                              From  => FA.Start_Vertex,
                              To    => FA.End_Vertex,
                              Var   => Change_Variant (Key_I, Normal_Use),
                              Tag   => Create_Tag ("uninitialized", Key_I));

                        elsif Atr_U.Is_Function_Return then
                           --  This is actually a totally different
                           --  error. It means we have a path where we
                           --  do not return from the function.
                           Error_Msg_Flow
                             (Msg => "function & might not return",
                              G   => FA.PDG,
                              Loc => FA.Start_Vertex,
                              F   => Key_I,
                              Tag => Create_Tag ("noreturn", Key_I));
                           Mark_Definition_Free_Path
                             (E_Loc => FA.Start_Vertex,
                              From  => FA.Start_Vertex,
                              To    => FA.End_Vertex,
                              Var   => Change_Variant (Key_I, Normal_Use),
                              Tag   => Create_Tag ("noreturn", Key_I));

                        elsif Atr_U.Is_Export then
                           --  As we don't have a global, but an
                           --  export, it means we must be dealing
                           --  with a parameter.
                           case Key_I.Kind is
                              when Record_Field =>
                                 Error_Msg_Flow
                                   (Msg => "component & of formal parameter"
                                      & " might not be set",
                                    G   => FA.PDG,
                                    Loc => V_Use,
                                    F   => Key_I,
                                    Tag => Create_Tag ("uninitialized",
                                                       Key_I));
                              when others =>
                                 Error_Msg_Flow
                                   (Msg => "formal parameter &"
                                      & " might not be set",
                                    G   => FA.PDG,
                                    Loc => V_Use,
                                    F   => Key_I,
                                    Tag => Create_Tag ("uninitialized",
                                                       Key_I));
                           end case;
                           Mark_Definition_Free_Path
                             (E_Loc => V_Use,
                              From  => FA.Start_Vertex,
                              To    => FA.End_Vertex,
                              Var   => Change_Variant (Key_I, Normal_Use),
                              Tag   => Create_Tag ("uninitialized", Key_I));

                        else
                           --  We are dealing with a local variable,
                           --  so we don't care if there is a path
                           --  where it is not set.
                           null;
                        end if;
                     else
                        Error_Msg_Flow
                          (Msg => "use of uninitialized variable &",
                           G   => FA.PDG,
                           Loc => V_Use,
                           F   => Key_I,
                           Tag => Create_Tag ("uninitialized"));
                        Mark_Definition_Free_Path
                          (E_Loc => V_Use,
                           From  => FA.Start_Vertex,
                           To    => V_Use,
                           Var   => Change_Variant (Key_I, Normal_Use),
                           Tag   => Create_Tag ("uninitialized", Key_I));
                     end if;
                  end;
               end loop;
            end if;
         end;
      end loop;
   end Find_Use_Of_Uninitialised_Variables;

   --------------------------
   -- Find_Stable_Elements --
   --------------------------

   procedure Find_Stable_Elements (FA : Flow_Analysis_Graphs) is
      Done      : Boolean       := False;
      Tmp       : Flow_Graphs.T := FA.DDG.Create;
      Is_Stable : Boolean;
   begin
      for Loop_Id of FA.Loops loop
         Done := False;
         while not Done loop
            Done := True;
            for N_Loop of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
               declare
                  Atr : V_Attributes := Tmp.Get_Attributes (N_Loop);
               begin
                  if Atr.Loops.Contains (Loop_Id) then
                     --  For all nodes in the loop, do:

                     --  We start by checking if the used variables
                     --  contain the loop parameter for our loop.
                     if Present (Loop_Parameter_From_Loop (Loop_Id)) then
                        Is_Stable := not Atr.Variables_Used.Contains
                          (Direct_Mapping_Id
                             (Loop_Parameter_From_Loop (Loop_Id)));
                     else
                        Is_Stable := True;
                     end if;

                     --  We then check if we have at least one
                     --  in-neighbour from "outside" the loop.
                     if Is_Stable then
                        for V of FA.PDG.Get_Collection
                          (N_Loop, Flow_Graphs.In_Neighbours) loop
                           if Tmp.Get_Attributes (V).Loops.Contains
                             (Loop_Id) then
                              Is_Stable := False;
                              exit;
                           end if;
                        end loop;
                     end if;

                     if Is_Stable then
                        --  Remove from the loop
                        Atr.Loops.Delete (Loop_Id);
                        Tmp.Set_Attributes (N_Loop, Atr);

                        --  Complain
                        Error_Msg_Flow (Msg => "stable",
                                        G   => FA.PDG,
                                        Loc => N_Loop);

                        --  There might be other stable elements now.
                        Done := False;
                     end if;
                  end if;
               end;
            end loop;
         end loop;
      end loop;
   end Find_Stable_Elements;

   -------------------------
   -- Find_Unused_Objects --
   -------------------------

   procedure Find_Unused_Objects (FA : Flow_Analysis_Graphs)
   is
      Used_Ids   : Vertex_Sets.Set := Vertex_Sets.Empty_Set;
      Entire_Ids : Vertex_Sets.Set := Vertex_Sets.Empty_Set;
   begin
      --  First we collect a set of all unused inputs.
      for V_Initial of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            I_F       : constant Flow_Id := FA.PDG.Get_Key (V_Initial);
            V_Final   : Flow_Graphs.Vertex_Id;
            F_F       : Flow_Id;
            Is_Unused : Boolean := False;
         begin
            if I_F.Variant = Initial_Value then
               --  For all 'initial vertices which have precisely one
               --  link...
               if FA.PDG.Out_Neighbour_Count (V_Initial) = 1 then
                  for V of FA.PDG.Get_Collection
                    (V_Initial, Flow_Graphs.Out_Neighbours)
                  loop
                     V_Final := V;
                  end loop;
                  F_F := FA.PDG.Get_Key (V_Final);
                  --  If that one link goes directly to the final use
                  --  vertex and its the only link...
                  if F_F.Variant = Final_Value and then
                    FA.PDG.In_Neighbour_Count (V_Final) = 1 then
                     --  then we are dealing with an unused object.
                     Is_Unused := True;
                  end if;
               end if;

               --  Note the entire variable.
               declare
                  P : Flow_Graphs.Vertex_Id := V_Initial;
               begin
                  while P /= Flow_Graphs.Null_Vertex loop
                     if FA.CFG.Parent (P) = Flow_Graphs.Null_Vertex then
                        Entire_Ids.Include (P);
                        exit;
                     end if;
                     P := FA.CFG.Parent (P);
                  end loop;
               end;

               --  Flag up records used.
               if not Is_Unused then
                  declare
                     P : Flow_Graphs.Vertex_Id := V_Initial;
                  begin
                     while P /= Flow_Graphs.Null_Vertex loop
                        Used_Ids.Include (P);
                        P := FA.CFG.Parent (P);
                     end loop;
                  end;
               end if;
            end if;
         end;
      end loop;

      --  Now that we have this set we can issue error messages. We
      --  can't do it inline because we need to pay special attention
      --  to records.
      for V of Entire_Ids loop
         if not Used_Ids.Contains (V) then
            declare
               F : constant Flow_Id      := FA.PDG.Get_Key (V);
               A : constant V_Attributes := FA.PDG.Get_Attributes (V);
            begin
               if Is_Discriminant (F) then
                  --  Discriminants can never not be used.
                  null;
               elsif A.Is_Global then
                  --  We have an unused global, we need to give the
                  --  error on the subprogram, instead of the
                  --  global.
                  Error_Msg_Flow (Msg => "global & is not used",
                                  N   => Find_Global (FA.Subprogram, F),
                                  F1  => F);
               else
                  Error_Msg_Flow (Msg => "& is not used",
                                  G   => FA.PDG,
                                  Loc => V,
                                  F   => F);
               end if;
            end;
         end if;
      end loop;
   end Find_Unused_Objects;

   ---------------------
   -- Check_Contracts --
   ---------------------

   procedure Check_Contracts (FA : Flow_Analysis_Graphs)
   is
      function Find_Export (E : Entity_Id) return Node_Id;
      --  Looks through the depends aspect on FA.Subprogram and
      --  returns the node which represents E in the dependency for E.

      -----------------
      -- Find_Export --
      -----------------

      function Find_Export (E : Entity_Id) return Node_Id
      is
         Pragma_Depends : constant Node_Id :=
           Aspect_Rep_Item (Find_Aspect (FA.Subprogram, Aspect_Depends));
         pragma Assert
           (List_Length (Pragma_Argument_Associations (Pragma_Depends)) = 1);

         PAA : constant Node_Id :=
           First (Pragma_Argument_Associations (Pragma_Depends));
         pragma Assert (Nkind (PAA) = N_Pragma_Argument_Association);

         CA : constant List_Id := Component_Associations (Expression (PAA));

         Row : Node_Id;
         LHS : Node_Id;
      begin
         Row := First (CA);
         while Present (Row) loop
            LHS := First (Choices (Row));
            case Nkind (LHS) is
               when N_Aggregate =>
                  LHS := First (Expressions (LHS));
                  while Present (LHS) loop
                     if Entity (LHS) = E then
                        return LHS;
                     end if;
                     LHS := Next (LHS);
                  end loop;
               when N_Identifier =>
                  if Entity (LHS) = E then
                     return LHS;
                  end if;
               when N_Null =>
                  null;
               when others =>
                  Print_Node_Subtree (LHS);
                  raise Why.Unexpected_Node;
            end case;

            Row := Next (Row);
         end loop;
         raise Why.Unexpected_Node;
      end Find_Export;

      User_Deps   : Dependency_Maps.Map;
      Actual_Deps : Dependency_Maps.Map;

   begin --  Check_Contracts

      if not Has_Depends (FA.Subprogram) then
         --  If the user has not specified a dependency relation we
         --  have no work to do.
         return;
      end if;

      --  Obtain the dependency relation specified by the user.
      Get_Depends (FA.Subprogram,
                   User_Deps);
      Actual_Deps := Compute_Dependency_Relation (FA);

      --  If the user depds do not include something we have in the
      --  actual deps we will raise an appropriate error. We should
      --  however also sanity check there is nothing in the user
      --  dependencies which is *not* in the actual dependencies.

      for C in User_Deps.Iterate loop
         declare
            F_Out : constant Flow_Id := Dependency_Maps.Key (C);
         begin
            if not Actual_Deps.Contains (F_Out) then
               Error_Msg_Flow
                 (Msg => "& missing from null dependency",
                  N   => Find_Aspect (FA.Subprogram, Aspect_Depends),
                  F1  => F_Out);
            end if;
         end;
      end loop;

      --  We go through the actual dependencies because they are
      --  always complete.

      for C in Actual_Deps.Iterate loop
         declare
            F_Out  : constant Flow_Id          := Dependency_Maps.Key (C);
            A_Deps : constant Flow_Id_Sets.Set := Dependency_Maps.Element (C);
            U_Deps : Flow_Id_Sets.Set;

            Missing_Deps : Ordered_Flow_Id_Sets.Set;
            Wrong_Deps   : Ordered_Flow_Id_Sets.Set;

            Proceed_With_Analysis : Boolean := True;
         begin
            if F_Out = Null_Flow_Id then
               --  The null dependency is special: it may not be
               --  present in the user dependency because null => null
               --  would be super tedious to write.
               if User_Deps.Contains (Null_Flow_Id) then
                  U_Deps := User_Deps (Null_Flow_Id);
               else
                  U_Deps := Flow_Id_Sets.Empty_Set;
               end if;
            elsif User_Deps.Contains (F_Out) then
               U_Deps := User_Deps (F_Out);
            else
               if F_Out.Kind = Magic_String then
                  Global_Required (FA, F_Out);
               else
                  Error_Msg_Flow
                    ("expected to see & on the left-hand-side of" &
                       " a dependency relation",
                     Find_Aspect (FA.Subprogram, Aspect_Depends),
                     F_Out);
               end if;
               Proceed_With_Analysis := False;
            end if;

            --  If we mention magic strings anywhere, there is no
            --  point in proceeding as the dependency relation
            --  *cannot* be correct.

            if Proceed_With_Analysis then
               for Var of A_Deps loop
                  if Var.Kind = Magic_String then
                     Global_Required (FA, Var);
                     Proceed_With_Analysis := False;
                  end if;
               end loop;
            end if;

            --  If all is still well we now do a consistency check.

            if Proceed_With_Analysis then
               Missing_Deps := To_Ordered_Flow_Id_Set (A_Deps - U_Deps);
               Wrong_Deps   := To_Ordered_Flow_Id_Set (U_Deps - A_Deps);

               for Missing_Var of Missing_Deps loop
                  --  Something that the user dependency fails to
                  --  mention.
                  if F_Out = Null_Flow_Id then
                     Error_Msg_Flow
                       (Msg => "& missing from null dependency",
                        N   => Find_Aspect (FA.Subprogram, Aspect_Depends),
                        F1  => Missing_Var);
                  else
                     Error_Msg_Flow
                       (Msg => "& depends on &",
                        N   => Find_Export (Get_Direct_Mapping_Id (F_Out)),
                        F1  => F_Out,
                        F2  => Missing_Var);
                     --  !!! show path
                  end if;
               end loop;

               for Wrong_Var of Wrong_Deps loop
                  --  Something the user dependency claims, but does
                  --  not happen in reality.
                  if F_Out = Null_Flow_Id then
                     Error_Msg_Flow
                       (Msg => "& incorrectly included in null dependency",
                        N   => Find_Aspect (FA.Subprogram, Aspect_Depends),
                        F1  => Wrong_Var);
                     --  ??? show a path?
                  else
                     Error_Msg_Flow
                       (Msg => "& does not depend on &",
                        N   => Find_Export (Get_Direct_Mapping_Id (F_Out)),
                        F1  => F_Out,
                        F2  => Wrong_Var);
                  end if;
               end loop;

            end if;

         end;
      end loop;
   end Check_Contracts;

end Flow.Analysis;
