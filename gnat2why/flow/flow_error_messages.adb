------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                  F L O W _ E R R O R _ M E S S A G E S                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                Copyright (C) 2013-2019, Altran UK Limited                --
--                     Copyright (C) 2013-2019, AdaCore                     --
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

with Ada.Characters.Handling;   use Ada.Characters.Handling;
with Ada.Containers.Indefinite_Vectors;
with Ada.Strings.Unbounded;     use Ada.Strings.Unbounded;
with Ada.Text_IO;

with Assumption_Types;          use Assumption_Types;
with Atree;                     use Atree;
with Common_Containers;         use Common_Containers;
with Einfo;                     use Einfo;
with Errout;                    use Errout;
with Erroutc;                   use Erroutc;
with Flow_Refinement;           use Flow_Refinement;
with Flow_Utility;              use Flow_Utility;
with Gnat2Why.Counter_Examples; use Gnat2Why.Counter_Examples;
with Gnat2Why.Expr.Loops;
with Gnat2Why_Args;             use Gnat2Why_Args;
with Gnat2Why_Opts;             use Gnat2Why_Opts;
with GNATCOLL.Utils;            use GNATCOLL.Utils;
with Lib.Xref;
with Namet;                     use Namet;
with Nlists;                    use Nlists;
with Sem_Aux;                   use Sem_Aux;
with Sem_Util;                  use Sem_Util;
with Sinfo;                     use Sinfo;
with Sinput;                    use Sinput;
with Snames;                    use Snames;
with SPARK_Annotate;            use SPARK_Annotate;
with SPARK_Atree;
with SPARK_Util;                use SPARK_Util;
with SPARK_Util.Subprograms;    use SPARK_Util.Subprograms;
with Stringt;                   use Stringt;
with String_Utils;

package body Flow_Error_Messages is

   Flow_Msgs_Set : String_Sets.Set;
   --  Container with flow-related messages; used to prevent duplicate messages

   package Session_File_Maps is new Ada.Containers.Indefinite_Vectors
     (Index_Type => Session_Dir_ID, Element_Type => String, "=" => "=");

   Session_File_Map : Session_File_Maps.Vector;
   --  The list of session files that belong to this gnat2why invocation

   function Get_Explanation (N : Node_Id; Tag : VC_Kind) return String;
   --  @param N node associated to an unproved check
   --  @param Tag associated unproved check
   --  @result message part explaining why the check was not proved

   function Msg_Severity_To_String (Severity : Msg_Severity) return String;
   --  Transform the msg kind into a string, for the JSON output

   type Message_Id is new Integer range -1 .. Integer'Last;
   --  type used to identify a message issued by gnat2why

   function Is_Specified_Line (Slc : Source_Ptr) return Boolean;
   --  Returns True if command line arguments "--limit-line" and
   --  "--limit-section" were not given, or
   --  if the sloc in argument corresponds to the line specified by the
   --  "--limit-line" argument, or
   --  if the sloc in argument is inside the region specified by the
   --  "--limit-region" argument.

   function Compute_Message
     (Msg  : String;
      N    : Node_Id;
      F1   : Flow_Id := Null_Flow_Id;
      F2   : Flow_Id := Null_Flow_Id;
      F3   : Flow_Id := Null_Flow_Id)
      return String with
      Pre => (if Present (F2) then Present (F1)) and then
             (if Present (F3) then Present (F2));
   --  This function:
   --    * adds more precise location for generics and inlining
   --    * substitutes flow nodes

   function Compute_Sloc
     (N           : Node_Id;
      Place_First : Boolean := False)
      return Source_Ptr
   with Post => (if Present (N)
                 then Compute_Sloc'Result >= First_Source_Ptr
                 else Compute_Sloc'Result = No_Location);
   --  Computes a better sloc for reporting of results than the Ada Node by
   --  taking generics into account.
   --  @param N the node for which we compute the sloc; might be Empty (e.g.
   --           when called from proof for a VC that doesn't correspond to any
   --           node)
   --  @param Place_First set this boolean to true to obtain placement at the
   --                     first sloc of the node, instead of the topmost node
   --  @return a valid sloc or No_Location when called with Empty node

   procedure Add_Json_Msg
     (Suppr      : String_Id;
      Tag        : String;
      Severity   : Msg_Severity;
      Slc        : Source_Ptr;
      Msg_List   : in out GNATCOLL.JSON.JSON_Array;
      E          : Entity_Id;
      Msg_Id     : Message_Id;
      How_Proved : Prover_Category;
      Tracefile  : String := "";
      Cntexmp    : Cntexample_File_Maps.Map := Cntexample_File_Maps.Empty_Map;
      Check_Tree : JSON_Value;
      SD_Id      : Session_Dir_Base_ID := No_Session_Dir;
      VC_File    : String := "";
      VC_Loc     : Source_Ptr := No_Location;
      Stats      : Prover_Stat_Maps.Map := Prover_Stat_Maps.Empty_Map;
      Editor_Cmd : String := "");
   --  Note that VC_Loc is the location of the verification check as opposed to
   --  Slc which is the location of the first failing part of a VC (raised as
   --  location for messages).

   function Warning_Is_Suppressed
     (N   : Node_Id;
      Msg : String;
      F1  : Flow_Id := Null_Flow_Id;
      F2  : Flow_Id := Null_Flow_Id;
      F3  : Flow_Id := Null_Flow_Id)
      return String_Id;
   --  Check if the warning for the given node, message and flow id is
   --  suppressed. If the function returns No_String, the warning is not
   --  suppressed. If it returns Null_String_Id the warning is suppressed,
   --  but no reason has been given. Otherwise, the String_Id of the reason
   --  is provided.

   function Print_Regular_Msg
     (Msg          : String;
      Slc          : Source_Ptr;
      Severity     : Msg_Severity;
      Continuation : Boolean := False)
      return Message_Id;
   --  Print a regular error, warning or info message using the frontend
   --  mechanism. Return an Id which can be used to identify this message.

   function Vertex_Sloc_Location
     (G   : Flow_Graphs.Graph;
      M   : Attribute_Maps.Map;
      V   : Flow_Graphs.Vertex_Id;
      Sep : Character := ':') return String;
   --  Obtain the location for the given vertex as in "foo.adb:12"

   Flow_Msgs : GNATCOLL.JSON.JSON_Array;
   --  This will hold all of the emitted flow messages in JSON format

   Proof_Msgs : GNATCOLL.JSON.JSON_Array;

   use type Flow_Graphs.Vertex_Id;

   function Escape (S : String) return String;
   --  Escape any special characters used in the error message (for example
   --  transforms "=>" into "='>" as > is a special insertion character. We
   --  also escape capital letters.

   function Substitute
     (S    : Unbounded_String;
      F    : Flow_Id;
      Flag : Source_Ptr)
      return Unbounded_String;
   --  Find the first '&' or '%' and substitute with the given flow id, with or
   --  without enclosing quotes respectively. Alternatively, '#' works like
   --  '&', but is followed by a line reference. Use '@' to substitute only
   --  with sloc of F.

   File_Counter : Natural := 0;
   Message_Id_Counter : Message_Id := 0;
   No_Message_Id : constant Message_Id := -1;

   Last_Suppressed : Boolean := False;
   Last_Suppr_Str  : String_Id := No_String;
   --  Used by Error_Msg_Flow to suppress continuation messages of suppressed
   --  messages. We need to know if a message was suppressed the last time, and
   --  the suppression reason, if any.

   ---------------------
   -- Compute_Message --
   ---------------------

   function Compute_Message
     (Msg  : String;
      N    : Node_Id;
      F1   : Flow_Id := Null_Flow_Id;
      F2   : Flow_Id := Null_Flow_Id;
      F3   : Flow_Id := Null_Flow_Id)
      return String
   is
      M : Unbounded_String := To_Unbounded_String (Msg);
   begin
      if Present (F1) then
         M := Substitute (M, F1, Sloc (N));
         if Present (F2) then
            M := Substitute (M, F2, Sloc (N));
            if Present (F3) then
               M := Substitute (M, F3, Sloc (N));
            end if;
         end if;
      end if;

      if Instantiation_Location (Sloc (N)) /= No_Location then

         --  If we are dealing with an instantiation of a generic we change the
         --  message to point at the implementation of the generic and we
         --  mention where the generic is instantiated.

         declare
            Loc     : Source_Ptr := Sloc (First_Node (N));
            File    : Unbounded_String;
            Line    : Physical_Line_Number;
            Context : Unbounded_String;
         begin
            loop
               exit when Instantiation_Location (Loc) = No_Location;

               --  Any change to the strings below should be reflected in GPS
               --  plugin spark2014.py, so that the unit for a given message is
               --  correctly computed.

               Context :=
                 To_Unbounded_String
                   (if Comes_From_Inlined_Body (Loc) then
                      ", in call inlined at "
                    elsif Comes_From_Inherited_Pragma (Loc) then
                      ", in inherited contract at "
                    else ", in instantiation at ");

               Loc := Instantiation_Location (Loc);
               File := To_Unbounded_String (File_Name (Loc));
               Line := Get_Physical_Line_Number (Loc);
               Append (M, Context & File & ":" & Image (Integer (Line), 1));
            end loop;
         end;
      end if;
      return To_String (M);
   end Compute_Message;

   ------------------
   -- Compute_Sloc --
   ------------------

   function Compute_Sloc
     (N           : Node_Id;
      Place_First : Boolean := False) return Source_Ptr
   is
      Slc : Source_Ptr :=
        (if Place_First
         then Safe_First_Sloc (N)
         else Sloc (N));
   begin
      if Instantiation_Location (Slc) /= No_Location then
         --  If we are dealing with an instantiation of a generic we change the
         --  message to point at the implementation of the generic and we
         --  mention where the generic is instantiated.
         Slc := Original_Location (Slc);
      end if;
      return Slc;
   end Compute_Sloc;

   --------------------------
   -- Vertex_Sloc_Location --
   --------------------------

   function Vertex_Sloc_Location
     (G   : Flow_Graphs.Graph;
      M   : Attribute_Maps.Map;
      V   : Flow_Graphs.Vertex_Id;
      Sep : Character := ':') return String
   is
      N  : constant Node_Or_Entity_Id := Error_Location (G, M, V);
      SI : constant Source_File_Index := Get_Source_File_Index (Sloc (N));
   begin
      return Get_Name_String (File_Name (SI)) & Sep &
        Get_Logical_Line_Number_Img (Sloc (N));
   end Vertex_Sloc_Location;

   --------------------
   -- Error_Location --
   --------------------

   function Error_Location
     (G : Flow_Graphs.Graph;
      M : Attribute_Maps.Map;
      V : Flow_Graphs.Vertex_Id) return Node_Or_Entity_Id
   is
      Loc : constant Node_Or_Entity_Id := M (V).Error_Location;
   begin
      if Present (Loc) then
         return Loc;
      else
         declare
            K : Flow_Id renames G.Get_Key (V);

         begin
            case K.Kind is
               when Direct_Mapping | Record_Field =>
                  return Get_Direct_Mapping_Id (K);
               when others =>
                  raise Program_Error;
            end case;
         end;
      end if;
   end Error_Location;

   --------------------
   -- Error_Msg_Flow --
   --------------------

   procedure Error_Msg_Flow
     (E            : Entity_Id;
      Msg          : String;
      Severity     : Msg_Severity;
      N            : Node_Id;
      Suppressed   : out Boolean;
      F1           : Flow_Id       := Null_Flow_Id;
      F2           : Flow_Id       := Null_Flow_Id;
      F3           : Flow_Id       := Null_Flow_Id;
      Tag          : Flow_Tag_Kind := Empty_Tag;
      SRM_Ref      : String        := "";
      Tracefile    : String        := "";
      Continuation : Boolean       := False)
   is
      Msg2 : constant String :=
        Msg &
        (if CWE and Severity /= Info_Kind then CWE_Message (Tag) else "") &
        (if SRM_Ref'Length > 0 then " (SPARK RM " & SRM_Ref & ")" else "");

      Attach_Node : constant Node_Id :=
        (if Instantiation_Location (Sloc (Original_Node (N))) = No_Location
         then N
         else Original_Node (N));
      --  Node where the message is attached. For nodes coming from inlining
      --  for proof and instantiations of generic units their Slocs is set to
      --  the point of inlining/instantiation. We detect such nodes and attach
      --  the message to the non-inlined/non-instantiated location, which is
      --  kept in Original_Node.
      --
      --  Note: we cannot blindly call Original_Node, because for aggregate
      --  notation (e.g. "Depends => ((Foo, Bar) => null)") it points to
      --  N_Aggregate whose Sloc is on the opening bracket (this is perhaps an
      --  artefact from parsing) and not to the component entity.

      Msg3 : constant String     := Compute_Message (Msg2, Attach_Node,
                                                     F1, F2, F3);
      Slc  : constant Source_Ptr := Compute_Sloc (Attach_Node);

      Msg_Str : constant String :=
        Msg3 &
        Source_Ptr'Image (Slc) &
        Integer'Image (Msg_Severity'Pos (Severity));

      Suppr  : String_Id  := No_String;
      Msg_Id : Message_Id;

      Dummy    : String_Sets.Cursor;
      Inserted : Boolean;

   --  Start of processing for Error_Msg_Flow

   begin
      --  If the message we are about to emit has already been emitted in the
      --  past then do nothing.

      Flow_Msgs_Set.Insert (New_Item => Msg_Str,
                            Position => Dummy,
                            Inserted => Inserted);

      if Inserted then

         --  If we are in mode check_all then we just report messages related
         --  to marking (filtered by Error_Kind severity) and that is why we
         --  suppress all the others.

         if Check_All_Mode then
            case Severity is
               when Error_Kind =>
                  Suppressed := False;
               when others =>
                  Suppressed := True;
            end case;
         else
            case Severity is
               when Warning_Kind =>
                  Suppr := Warning_Is_Suppressed (N, Msg3, F1, F2, F3);
                  Suppressed := Suppr /= No_String;

               when Info_Kind =>
                  Suppressed := Report_Mode = GPR_Fail;

               when Check_Kind =>
                  declare
                     Is_Annot : Boolean;
                     Info     : Annotated_Range;
                  begin
                     Check_Is_Annotated (N, Msg3, True, Is_Annot, Info);
                     if Is_Annot then
                        Suppr := Info.Reason;
                     end if;
                  end;
                  Suppressed := Suppr /= No_String;

               when Error_Kind =>
               --  Set the error flag if we have an error message. Note that
               --  warnings do not count as errors here, they should not
               --  prevent us going to proof. The errout mechanism already
               --  deals with the warnings-as-errors handling for the whole
               --  unit.
                  Suppressed       := False;
                  Found_Flow_Error := True;
            end case;
         end if;

         --  In the case of a continuation message, also take into account the
         --  result of the last non-continuation message. Do not simply take
         --  over the result, but merge it with the results of the continuation
         --  message, so that one can also suppress only the continuation
         --  message.

         if Continuation then
            Suppressed := Suppressed or Last_Suppressed;
            Suppr := (if Suppr = No_String then Last_Suppr_Str else Suppr);
         end if;

         --  Print the message except when it's suppressed. Additionally, if
         --  command line argument "--limit-line" was given, only issue the
         --  warning if it is to be emitted on the specified line (errors are
         --  emitted anyway).

         if not Suppressed and then Is_Specified_Line (Slc) then
            Msg_Id := Print_Regular_Msg (Msg3, Slc, Severity, Continuation);
         else
            Msg_Id := No_Message_Id;
         end if;

         --  In check_all mode, we don't want any messages to appear even in
         --  the JSON output, unless they are error messages.

         if not Check_All_Mode or else Severity = Error_Kind then
            Add_Json_Msg
              (Suppr      => Suppr,
               Tag        => Flow_Tag_Kind'Image (Tag),
               How_Proved => PC_Flow,
               Severity   => Severity,
               Slc        => Slc,
               Msg_List   => Flow_Msgs,
               E          => E,
               Tracefile  => Tracefile,
               Check_Tree => Create_Object,
               Msg_Id     => Msg_Id);
         end if;

      else
         Suppressed := True;
      end if;

      --  In case of a non-continuation message, store the suppressed/justified
      --  info.

      if not Continuation then
         Last_Suppressed := Suppressed;
         Last_Suppr_Str := Suppr;
      end if;
   end Error_Msg_Flow;

   procedure Error_Msg_Flow
     (FA           : in out Flow_Analysis_Graphs;
      Msg          : String;
      Severity     : Msg_Severity;
      N            : Node_Id;
      F1           : Flow_Id               := Null_Flow_Id;
      F2           : Flow_Id               := Null_Flow_Id;
      F3           : Flow_Id               := Null_Flow_Id;
      Tag          : Flow_Tag_Kind         := Empty_Tag;
      SRM_Ref      : String                := "";
      Path         : Vertex_Sets.Set       := Vertex_Sets.Empty_Set;
      Vertex       : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex;
      Continuation : Boolean               := False)
   is
      Vertex_Img : constant String :=
        Image (FA.CFG.Vertex_To_Natural (Vertex), 1);
      Debug_Msg  : constant String :=
        (if Gnat2Why_Args.Flow_Advanced_Debug
           and then Vertex /= Flow_Graphs.Null_Vertex
         then Msg & " <" & Vertex_Img & ">"
         else Msg);

      Suppressed : Boolean;

      function Write_Tracefile (Set : Vertex_Sets.Set) return String;
      --  Writes the tracefile from the given Set and returns the filename

      ---------------------
      -- Write_Tracefile --
      ---------------------

      function Write_Tracefile (Set : Vertex_Sets.Set) return String
      is
         FD        : Ada.Text_IO.File_Type;
         Tracefile : constant String := Fresh_Trace_File;
      begin
         Ada.Text_IO.Create (FD, Ada.Text_IO.Out_File, Tracefile);

         for V of Set loop
            declare
               F : Flow_Id renames FA.PDG.Get_Key (V);

            begin
               --  ??? we should only print vertices whose Atr.Is_Program_Node
               --  is True (taking into account various special-cases).
               if F.Kind = Direct_Mapping then
                  Ada.Text_IO.Put_Line
                    (FD, Vertex_Sloc_Location (FA.PDG, FA.Atr, V));
               end if;
            end;
         end loop;

         Ada.Text_IO.Close (FD);

         return Tracefile;
      end Write_Tracefile;

      Tracefile : constant String :=
        (if Continuation or else Path.Is_Empty
         then ""
         else Write_Tracefile (Path));

   --  Start of processing for Error_Msg_Flow

   begin
      Error_Msg_Flow (E            => FA.Spec_Entity,
                      Msg          => Debug_Msg,
                      Severity     => Severity,
                      N            => N,
                      Suppressed   => Suppressed,
                      F1           => F1,
                      F2           => F2,
                      F3           => F3,
                      Tag          => Tag,
                      SRM_Ref      => SRM_Ref,
                      Tracefile    => Tracefile,
                      Continuation => Continuation);

      --  Set the Errors_Or_Warnings flag to True for this entity if we are
      --  with anything but a suppressed warning.

      if not Suppressed then
         FA.Errors_Or_Warnings := True;

         if Tag in Data_Dependency_Tag then
            FA.Data_Dependency_Errors := True;
         end if;

         if Tag in Flow_Dependency_Tag then
            FA.Flow_Dependency_Errors := True;
         end if;
      end if;
   end Error_Msg_Flow;

   ---------------------
   -- Error_Msg_Proof --
   ---------------------

   procedure Error_Msg_Proof
     (N           : Node_Id;
      Msg         : String;
      Is_Proved   : Boolean;
      Tag         : VC_Kind;
      Cntexmp     : JSON_Value;
      Check_Tree  : JSON_Value;
      VC_File     : String;
      VC_Loc      : Node_Id;
      Editor_Cmd  : String;
      E           : Entity_Id;
      How_Proved  : Prover_Category;
      SD_Id       : Session_Dir_Base_ID;
      Stats       : Prover_Stat_Maps.Map;
      Place_First : Boolean)
   is

      function Get_Severity
        (N         : Node_Id;
         Is_Proved : Boolean;
         Tag       : VC_Kind) return Msg_Severity;
      --  @result Severity of the proof message

      ------------------
      -- Get_Severity --
      ------------------

      function Get_Severity
        (N         : Node_Id;
         Is_Proved : Boolean;
         Tag       : VC_Kind) return Msg_Severity
      is
         Result : Msg_Severity;

      begin
         if Tag in VC_Warning_Kind then
            pragma Assert (Is_Proved);
            Result := Warning_Kind;

         elsif Is_Proved then
            Result := Info_Kind;

         --  Range checks on concatenation of strings are likely to be
         --  unprovable because argument types do not bound the size of the
         --  strings being concatenated. Issue a low severity message in such
         --  cases.

         elsif Tag = VC_Range_Check
           and then Is_String_Type (Etype (N))
           and then Nkind (N) = N_Op_Concat
         then
            Result := Low_Check_Kind;

         --  Default for unproved checks is to issue a medium severity message

         else
            Result := Medium_Check_Kind;
         end if;

         return Result;
      end Get_Severity;

      Msg2   : constant String     := Compute_Message (Msg, N);
      Slc    : constant Source_Ptr := Compute_Sloc (N, Place_First);
      VC_Slc : constant Source_Ptr := Compute_Sloc (VC_Loc, Place_First);

      Pretty_Cntexmp  : constant Cntexample_File_Maps.Map :=
        Create_Pretty_Cntexmp (From_JSON (Cntexmp), Slc);
      One_Liner : constant String :=
        (if Pretty_Cntexmp.Is_Empty then ""
         else Get_Cntexmp_One_Liner (Pretty_Cntexmp, Slc));
      Msg3     : constant String :=
        (if One_Liner = "" then Msg2
         else (Msg2 & " (e.g. when " & One_Liner & ")"));
      Severity : constant Msg_Severity := Get_Severity (N, Is_Proved, Tag);
      Suppr    : String_Id := No_String;
      Msg_Id   : Message_Id := No_Message_Id;
      Is_Annot : Boolean;
      Info     : Annotated_Range;

   --  Start of processing for Error_Msg_Proof

   begin

      --  Proof (why3) will only report messages that are relevant wrt
      --  limit-line option, but Interval and CodePeer messages will be
      --  issued for all lines. So we add this extra filter here.

      if How_Proved in PC_Interval | PC_Codepeer
        and then not Is_Specified_Line (Slc)
      then
         return;
      end if;

      --  The call to Check_Is_Annotated needs to happen on all paths, even
      --  though we only need the info in the Check_Kind path. The reason is
      --  that also in the Info_Kind case, we want to know whether the check
      --  corresponds to a pragma Annotate.

      Check_Is_Annotated (N, Msg, Severity in Check_Kind, Is_Annot, Info);

      case Severity is
         when Check_Kind =>
            if Is_Annot then
               Suppr := Info.Reason;
            else
               declare
                  Expl : constant String := Get_Explanation (N, Tag);
                  Msg4 : constant String :=
                    (if Expl = "" then Msg3
                     else Msg3 & " [possible explanation: " & Expl & "]");
               begin
                  Msg_Id := Print_Regular_Msg (Msg4, Slc, Severity);
               end;
            end if;
         when Info_Kind =>
            if Report_Mode /= GPR_Fail then
               Msg_Id := Print_Regular_Msg (Msg3, Slc, Severity);
            end if;
         when Warning_Kind =>
            Msg_Id := Print_Regular_Msg (Msg3, Slc, Severity);
         when Error_Kind =>
            --  cannot happen
            raise Program_Error;
      end case;

      Add_Json_Msg
        (Suppr       => Suppr,
         Tag         => VC_Kind'Image (Tag),
         Severity    => Severity,
         Slc         => Slc,
         Msg_List    => Proof_Msgs,
         Msg_Id      => Msg_Id,
         E           => E,
         Cntexmp     => Pretty_Cntexmp,
         Check_Tree  => Check_Tree,
         SD_Id       => SD_Id,
         VC_File     => VC_File,
         VC_Loc      => VC_Slc,
         How_Proved  => How_Proved,
         Stats       => Stats,
         Editor_Cmd  => Editor_Cmd);

   end Error_Msg_Proof;

   ------------
   -- Escape --
   ------------

   function Escape (S : String) return String is
      R : Unbounded_String := Null_Unbounded_String;
   begin
      for C of S loop
         if C in '%' | '$' | '{' | '*' | '&' | '#' |
                 '}' | '@' | '^' | '>' | '!' | '?' |
                 '<' | '`' | ''' | '\' | '|' | '[' |
                 ']'
           or else Is_Upper (C)
         then
            Append (R, "'");
         end if;

         Append (R, C);
      end loop;

      return To_String (R);
   end Escape;

   ----------------------
   -- Fresh_Trace_File --
   ----------------------

   function Fresh_Trace_File return String is
      Result : constant String :=
        Unit_Name & "__flow__" & Image (File_Counter, 1) & ".trace";
   begin
      File_Counter := File_Counter + 1;
      return Result;
   end Fresh_Trace_File;

   ---------------------
   -- Get_Explanation --
   ---------------------

   function Get_Explanation (N : Node_Id; Tag : VC_Kind) return String is

      -----------------------
      -- Local subprograms --
      -----------------------

      function Is_Stmt_Or_Prag_Or_Decl (N : Node_Id) return Boolean is
        (Nkind (N) in N_Procedure_Call_Statement
                    | N_Pragma
                    | N_Statement_Other_Than_Procedure_Call
                    | N_Declaration
                    | N_Later_Decl_Item
                    | N_Handled_Sequence_Of_Statements);

      function Enclosing_Stmt_Or_Prag_Or_Decl is new
        First_Parent_With_Property (Is_Stmt_Or_Prag_Or_Decl);

      subtype Explain_Node_Kind is Node_Kind
        with Static_Predicate =>
          Explain_Node_Kind in N_Empty
                             | N_Assignment_Statement
                             | N_Procedure_Call_Statement
                             | N_Loop_Statement
                             | N_Subprogram_Body
                             | N_Subprogram_Declaration;

      function Explain_Output_Variables
        (Vars : Flow_Id_Sets.Set) return Unbounded_String;
      --  Return part of the explanation listing the bounds and discriminants
      --  of output variables in [Vars].

      function Explain_Variables
        (Vars : Flow_Id_Sets.Set;
         Map  : Flow_Id_Surjection.Map := Flow_Id_Surjection.Empty_Map)
         return Unbounded_String;
      --  Return part of the explanation listing the variables in [Vars], using
      --  [Map] for the translation from actuals to formals in a call.

      function Get_Line_Number (N : Node_Id; Flag : Source_Ptr) return String;
      --  Return a string describing the location Flag wrt the origin of the
      --  message on node N.

      function Get_Loop_Condition_Or_Variable
        (Stmt : Node_Id) return Node_Or_Entity_Id
      with
        Post => No (Get_Loop_Condition_Or_Variable'Result)
          or else Nkind (Get_Loop_Condition_Or_Variable'Result) in N_Subexpr
          or else
            Ekind (Get_Loop_Condition_Or_Variable'Result) = E_Loop_Parameter;
      --  Get the loop condition for a WHILE loop or the loop variable for a
      --  FOR loop. Return Empty for a plain loop.

      function Get_Pre_Post
        (Proc    : Entity_Id;
         Prag_Id : Pragma_Id) return Node_Lists.List;
      --  Return the list of expressions mentioned in a precondition or a
      --  postcondition, including the class-wide ones.

      function Get_Previous_Explain_Node (N : Node_Id) return Node_Id with
        Pre  => Is_Stmt_Or_Prag_Or_Decl (N),
        Post => Nkind (Get_Previous_Explain_Node'Result) in Explain_Node_Kind;
      --  Return the statement preceding [N] that is relevant in explaining an
      --  unproved property. This might be:
      --    - Empty if no relevant statement was found.
      --    - an assignment statement, as it may assign a value to a variable,
      --      in a way that enough is known to prove the property regarding
      --      this variable.
      --    - a procedure call, as it may modify the value of a variable
      --      without stating how this variable was modified in its
      --      postcondition.
      --    - a loop statement, as it may modify the value of a variable
      --      without stating how this variable was modified in its
      --      loop invariant.
      --    - a subprogram body, as it may take a variable in input without
      --      stating how this variable should be constrained in
      --      a precondition.

      function Get_Variables_From_Expr
        (Expr    : Node_Id;
         Context : Node_Id;
         Map     : Flow_Id_Surjection.Map := Flow_Id_Surjection.Empty_Map)
         return Flow_Id_Sets.Set
      with
        Pre => Nkind (Expr) in N_Subexpr;
      --  @param Expr expression
      --  @param Context relevant context for interpreting flow ids
      --  @param Map map of flow ids to apply on expression to find additional
      --         variables to retrieve
      --  Extract all the entire variables corresponding to flow ids in the
      --  expression [Expr].

      function Get_Variables_From_Node
        (N   : Node_Id;
         Tag : VC_Kind) return Flow_Id_Sets.Set;
      --  Return the set of flow ids to consider for the check of kind Tag
      --  associated to node N.

      function Has_Attribute_Result (N : Node_Id) return Boolean;
      --  Return whether N refers to some attribute Func'Result

      function Has_Post_State (N : Node_Id) return Boolean;
      --  Return whether N as a node inside a postcondition possibly refers to
      --  some post state of the subprogram.

      ------------------------------
      -- Explain_Output_Variables --
      ------------------------------

      function Explain_Output_Variables
        (Vars : Flow_Id_Sets.Set) return Unbounded_String
      is
         Nodes     : constant Node_Sets.Set := To_Node_Set (Vars);
         Expl      : Unbounded_String;
         First_Var : Boolean := True;
      begin
         for V of Nodes loop
            if Is_Array_Type (Etype (V))
              or else Has_Discriminants (Etype (V))
            then
               if First_Var then
                  First_Var := False;
               else
                  Append (Expl, " or ");
               end if;

               declare
                  Id    : constant Flow_Id := Direct_Mapping_Id (V);
                  Str   : constant String :=
                    Flow_Id_To_String (Id, Pretty => True);
                  Discr : Entity_Id;
               begin
                  if Is_Array_Type (Etype (V)) then
                     Append (Expl, Str & "'Length");
                     Append (Expl, " or " & Str & "'First");
                     Append (Expl, " or " & Str & "'Last");

                  else
                     Append (Expl, Str & "'Constrained");

                     Discr := First_Discriminant (Etype (V));
                     while Present (Discr) loop
                        Append (Expl, " or " & Str & "."
                                & Flow_Id_To_String (Direct_Mapping_Id (Discr),
                                                     Pretty => True));
                        Next_Discriminant (Discr);
                     end loop;
                  end if;
               end;
            end if;
         end loop;
         return Expl;
      end Explain_Output_Variables;

      -----------------------
      -- Explain_Variables --
      -----------------------

      function Explain_Variables
        (Vars : Flow_Id_Sets.Set;
         Map  : Flow_Id_Surjection.Map := Flow_Id_Surjection.Empty_Map)
         return Unbounded_String
      is
         Expl      : Unbounded_String;
         First_Var : Boolean := True;
      begin
         for V of To_Ordered_Flow_Id_Set (Vars) loop
            if First_Var then
               First_Var := False;
            else
               Append (Expl, " and ");
            end if;

            if Map.Contains (V) then
               --  Only pretty-print actuals; formals will be pretty anyway
               Append (Expl, Flow_Id_To_String (Map (V))
                       & " (for argument "
                       & Flow_Id_To_String (V, Pretty => True)
                       & ")");
            else
               Append (Expl, Flow_Id_To_String (V, Pretty => True));
            end if;
         end loop;
         return Expl;
      end Explain_Variables;

      ---------------------
      -- Get_Line_Number --
      ---------------------

      --  This function was inspired by Erroutc.Set_Msg_Insertion_Line_Number
      --  to decide when to refer to the filename in the location.

      function Get_Line_Number (N : Node_Id; Flag : Source_Ptr) return String
      is
         Loc         : constant Source_Ptr := Sloc (N);
         Sindex_Loc  : constant Source_File_Index :=
           Get_Source_File_Index (Loc);
         Sindex_Flag : constant Source_File_Index :=
           Get_Source_File_Index (Flag);
         Fname       : File_Name_Type;
         Line        : constant String :=
           String_Utils.Trimi (Get_Physical_Line_Number (Flag)'Img, ' ');

      begin
         --  Use "at file-name:line-num" if reference is to other than the
         --  source file in which the unproved check message is placed.
         --  Note that we check full file names, rather than just the source
         --  indexes, to deal with generic instantiations from the current
         --  file.

         if Full_File_Name (Sindex_Loc) /= Full_File_Name (Sindex_Flag) then
            Fname := Reference_Name (Get_Source_File_Index (Flag));
            return "at " & Get_Name_String (Fname) & ":" & Line;

         --  If in current file, use text "at line line-num"

         else
            return "at line " & Line;
         end if;
      end Get_Line_Number;

      ------------------------------------
      -- Get_Loop_Condition_Or_Variable --
      ------------------------------------

      function Get_Loop_Condition_Or_Variable
        (Stmt : Node_Id) return Node_Or_Entity_Id
      is
         Scheme : constant Node_Id := Iteration_Scheme (Stmt);
      begin
         --  Case of a simple loop

         if No (Scheme) then
            return Empty;

         --  Case of a WHILE loop

         elsif Present (Condition (Scheme)) then
            return Condition (Scheme);

         --  Case of a FOR loop

         elsif Present (Loop_Parameter_Specification (Scheme)) then
            return Defining_Identifier (Loop_Parameter_Specification (Scheme));

         else
            pragma Assert (Present (Iterator_Specification (Scheme)));
            return Defining_Identifier (Iterator_Specification (Scheme));
         end if;
      end Get_Loop_Condition_Or_Variable;

      ------------------
      -- Get_Pre_Post --
      ------------------

      function Get_Pre_Post
        (Proc    : Entity_Id;
         Prag_Id : Pragma_Id) return Node_Lists.List
      is
         Prag       : Node_Lists.List :=
           Find_Contracts (Proc, Prag_Id);
         Class_Prag : constant Node_Lists.List :=
           Find_Contracts (Proc, Prag_Id, Classwide => True);
      begin
         SPARK_Util.Append (To => Prag, Elmts => Class_Prag);
         return Prag;
      end Get_Pre_Post;

      -------------------------------
      -- Get_Previous_Explain_Node --
      -------------------------------

      function Get_Previous_Explain_Node (N : Node_Id) return Node_Id is
         M : Node_Id;
      begin
         --  First look for a relevant node in the statements preceding [N] in
         --  the same list of statements.

         if Is_List_Member (N) then
            M := Prev (N);
            while Present (M) loop
               if Nkind (M) in Explain_Node_Kind then
                  return M;
               end if;
               Prev (M);
            end loop;
         end if;

         --  Then look at a suitable node up the chain from [N]

         M := Enclosing_Stmt_Or_Prag_Or_Decl (N);

         if Nkind (M) in Explain_Node_Kind then
            return M;

         --  If not done yet, continue looking from the parent node of [N] if
         --  possible.

         elsif Is_Stmt_Or_Prag_Or_Decl (M) then
            return Get_Previous_Explain_Node (M);

         --  Otherwise return Empty

         else
            return Empty;
         end if;
      end Get_Previous_Explain_Node;

      -----------------------------
      -- Get_Variables_From_Expr --
      -----------------------------

      function Get_Variables_From_Expr
        (Expr    : Node_Id;
         Context : Node_Id;
         Map     : Flow_Id_Surjection.Map := Flow_Id_Surjection.Empty_Map)
         return Flow_Id_Sets.Set
      is
         Expr_Vars : constant Flow_Id_Sets.Set :=
           Get_Variables_For_Proof (Expr, Context);
         Mapped_Vars : Flow_Id_Sets.Set;

         use type Flow_Id_Sets.Set;

      begin
         for V of Expr_Vars loop
            if Map.Contains (V) then
               Mapped_Vars.Include (Map (V));
            end if;
         end loop;

         return Expr_Vars or Mapped_Vars;
      end Get_Variables_From_Expr;

      -----------------------------
      -- Get_Variables_From_Node --
      -----------------------------

      function Get_Variables_From_Node
        (N   : Node_Id;
         Tag : VC_Kind) return Flow_Id_Sets.Set
      is
         Vars : Flow_Id_Sets.Set;
      begin
         --  For a precondition check on a call, retrieve the precondition of
         --  the called subprogram as source for the explanation, and translate
         --  back variables mentioned in the precondition into actuals.

         if Tag = VC_Precondition
           and then Nkind (N) in N_Subprogram_Call
         then
            Handle_Precondition_Check : declare
               Subp : constant Entity_Id := SPARK_Atree.Get_Called_Entity (N);
               Prag : constant Node_Id :=
                 Get_Pragma (Subp, Pragma_Precondition);
               Pre  : constant Node_Id :=
                 (if Present (Prag) then
                    Expression (First (Pragma_Argument_Associations (Prag)))
                  else Empty);

               Formal_To_Actual : Flow_Id_Surjection.Map;

               procedure Treat_Param
                 (Formal : Entity_Id; Actual : Node_Id);
               --  Fill the mapping formal->actual

               procedure Treat_Param
                 (Formal : Entity_Id; Actual : Node_Id)
               is
                  Var : Entity_Id;
                  Id  : Flow_Id;
               begin
                  if Ekind (Formal) in E_In_Parameter
                                     | E_In_Out_Parameter
                  then
                     Var := SPARK_Atree.Get_Enclosing_Object (Actual);

                     --  We only insert into the mapping when the actual is
                     --  rooted in a variable. A more elaborate solution would
                     --  consist in computing all the variables involved in the
                     --  actual expression.

                     if Present (Var) then
                        Id := Direct_Mapping_Id (Var);

                        --  Store the mapping formal->actual for possibly
                        --  replacing the formal by the actual when the
                        --  formal is mentioned in the precondition.

                        Formal_To_Actual.Insert
                          (Direct_Mapping_Id (Formal), Id);
                     end if;
                  end if;
               end Treat_Param;

               procedure Iterate_Call is new
                 SPARK_Atree.Iterate_Call_Parameters (Treat_Param);

            begin
               if Present (Pre) then
                  Iterate_Call (N);
                  Vars := Get_Variables_From_Expr (Pre, Pre, Formal_To_Actual);
               end if;
            end Handle_Precondition_Check;

         elsif Nkind (N) = N_Assignment_Statement then
            declare
               V : constant Entity_Id :=
                 SPARK_Atree.Get_Enclosing_Object (Name (N));
            begin
               Vars := Flow_Id_Sets.To_Set (Direct_Mapping_Id (V));
            end;

         --  As Get_Variables_For_Proof only apply to expressions, we do not
         --  try to get an explanation for other cases of procedure calls,
         --  i.e. when the check is not a precondition.

         elsif Nkind (N) = N_Procedure_Call_Statement then
            pragma Assert (Tag /= VC_Precondition);

         else
            pragma Assert (Nkind (N) in N_Subexpr
                           and then Nkind (N) /= N_Procedure_Call_Statement);

            Vars := Get_Variables_For_Proof (N, N);
         end if;

         return Vars;
      end Get_Variables_From_Node;

      --------------------------
      -- Has_Attribute_Result --
      --------------------------

      function Has_Attribute_Result (N : Node_Id) return Boolean is

         function Is_Function_Result (N : Node_Id) return Traverse_Result is
           (if Is_Attribute_Result (N)
            then Abandon
            else OK);

         function Check_Function_Result is
           new Traverse_More_Func (Is_Function_Result);

      --  Start of processing for Has_Attribute_Result

      begin
         return Check_Function_Result (N) = Abandon;
      end Has_Attribute_Result;

      --------------------
      -- Has_Post_State --
      --------------------

      --  This function is similar to the one in sem_util.adb to warn about
      --  postconditions which do not refer to the post state. We keep it
      --  separate in order to possibly evolve this version differently, as
      --  we can assume SPARK code here and query flow analysis for effects.

      function Has_Post_State (N : Node_Id) return Boolean is

         function Is_Post_State (N : Node_Id) return Traverse_Result;
         --  Attempt to find a construct that denotes a post-state. If this
         --  is the case, set flag Post_State_Seen.

         -------------------
         -- Is_Post_State --
         -------------------

         function Is_Post_State (N : Node_Id) return Traverse_Result is
            Ent : Entity_Id;

         begin
            if Nkind_In (N, N_Explicit_Dereference, N_Function_Call) then
               return Abandon;

            elsif Nkind_In (N, N_Expanded_Name, N_Identifier) then
               Ent := Entity (N);

               --  Treat an undecorated reference as OK

               if No (Ent)

                 --  A reference to an assignable entity is considered a
                 --  change in the post-state of a subprogram.

                 or else Is_Assignable (Ent)

                 --  The reference may be modified through a dereference

                 or else (Is_Access_Type (Etype (Ent))
                          and then Nkind (Parent (N)) =
                            N_Selected_Component)
               then
                  return Abandon;
               end if;

            elsif Nkind (N) = N_Attribute_Reference then
               if Attribute_Name (N) = Name_Old then
                  return Skip;

               elsif Attribute_Name (N) = Name_Result then
                  return Abandon;
               end if;
            end if;

            return OK;
         end Is_Post_State;

         function Find_Post_State is new Traverse_More_Func (Is_Post_State);

      --  Start of processing for Has_Post_State

      begin
         return Find_Post_State (N) = Abandon;
      end Has_Post_State;

      --  Local variables

      Enclosing_Subp : Entity_Id :=
        Lib.Xref.SPARK_Specific.Enclosing_Subprogram_Or_Library_Package (N);
      --  Approximate search for the enclosing subprogram or library package.
      --  It is fine to use this function here even if not always correct, as
      --  it's only used for adding or not an explanation.

   --  Start of processing for Get_Explanation

   begin
      --  Adjust the enclosing subprogram entity

      if Present (Enclosing_Subp) then
         Enclosing_Subp := Unique_Entity (Enclosing_Subp);
      end if;

      --  Only attempt explanation when the node associated to the unproved
      --  check is an expression, an assignment or a procedure call (which are
      --  part of N_Subexpr). When it's a procedure call, only handle the case
      --  where the VC is a precondition check.

      if Nkind (N) not in N_Subexpr | N_Assignment_Statement
        and then (if Nkind (N) = N_Procedure_Call_Statement
                  then Tag = VC_Precondition)
      then
         return "";

      --  Do not attempt to generate an explanation for a check inside a
      --  DIC procedure or an invariant procedure, as these are generated
      --  procedures on which the user can put no precondition.

      elsif Present (Enclosing_Subp)
        and then Is_Subprogram (Enclosing_Subp)
        and then (Is_DIC_Procedure (Enclosing_Subp)
                   or else Is_Invariant_Procedure (Enclosing_Subp))
      then
         return "";

      --  We do not relate the expression in return statements and the
      --  pseudo-variable Func'Result, hence it is better not to try to find
      --  an explanation for a check involving Func'Result.

      elsif Has_Attribute_Result (N) then
         return "";

      else
         declare
            Check_Vars  : Flow_Id_Sets.Set := Get_Variables_From_Node (N, Tag);
            --  Retrieve variables from the node associated to the failed
            --  proof. This set can be reduced during our traversal back in the
            --  control-flow graph, as we bump into assignments that provide a
            --  value to some variables.

            Restarted_Search : Boolean := False;
            --  Flag set to True if the search was restarted from the last
            --  statement of the subprogram. This is done for checks inside
            --  postconditions.

            Stmt        : Node_Id;
            Vars        : Flow_Id_Sets.Set;
            Ignore_Vars : Flow_Id_Sets.Set;
            Read_Vars   : Flow_Id_Sets.Set;
            Write_Vars  : Flow_Id_Sets.Set;
            Info_Vars   : Flow_Id_Sets.Set;
            Pragmas     : Node_Lists.List;
            Expl        : Unbounded_String;
            Prag_N      : Node_Id;

            use type Flow_Id_Sets.Set;

         begin
            --  Compute the enclosing pragma if any, for use later to decide
            --  when a subprogram declaration is a suitable explanation node.

            Prag_N := Enclosing_Stmt_Or_Prag_Or_Decl (N);

            if Nkind (Prag_N) /= N_Pragma then
               Prag_N := Empty;
            end if;

            --  Filter out variables which are generated by the compiler

            declare
               Internal_Vars : Flow_Id_Sets.Set;
            begin
               for V of Check_Vars loop
                  if V.Kind = Direct_Mapping
                    and then not Comes_From_Source (V.Node)
                  then
                     Internal_Vars.Insert (V);
                  end if;
               end loop;
               Check_Vars.Difference (Internal_Vars);
            end;

            --  Nothing to propagate if the set of checked variables is empty

            if Check_Vars.Is_Empty then
               return "";
            end if;

            --  Start looking for an explanation

            if Nkind (N) = N_Procedure_Call_Statement then
               Stmt := N;
            else
               Stmt := Enclosing_Stmt_Or_Prag_Or_Decl (N);
            end if;

            if No (Stmt) then
               return "";
            end if;

            Stmt := Get_Previous_Explain_Node (Stmt);

            while Present (Stmt) loop
               case Explain_Node_Kind'(Nkind (Stmt)) is
               when N_Empty =>
                  null;

               --  If we bump into an assignment to some entire variable, where
               --  the value assigned does not depend on any variable, then
               --  it's likely that the prover has all the relevant information
               --  about the value of this variable for the proof. Remove this
               --  variable from the set of variables tracked.

               when N_Assignment_Statement =>
                  declare
                     Lhs       : constant Node_Id := Name (Stmt);
                     Expr      : constant Node_Id := Expression (Stmt);
                     Var       : Entity_Id;
                     Id        : Flow_Id;
                     Expr_Vars : Flow_Id_Sets.Set;
                  begin
                     --  See if this is an assignment to an entire variable...

                     if Nkind (Lhs) in N_Has_Entity then
                        Var := Entity (Lhs);
                        Id  := Direct_Mapping_Id (Var);

                        --  and this variable is currently tracked...

                        if Check_Vars.Contains (Id) then
                           Expr_Vars := Get_Variables_For_Proof (Expr, N);

                           --  and it is assigned a value that does not depend
                           --  on any variable. In that case, remove the
                           --  variable from the set of variables tracked.

                           --  ??? Currently Expr_Vars may contain variables
                           --  that are only Proof_In globals to a call in
                           --  Expr, which ideally should be discarded here
                           --  for better precision.

                           if Expr_Vars.Is_Empty then
                              Check_Vars.Delete (Id);
                           end if;
                        end if;
                     end if;
                  end;

               when N_Procedure_Call_Statement =>
                  declare
                     Formal_To_Actual : Flow_Id_Surjection.Map;
                     Actual_To_Formal : Flow_Id_Surjection.Map;

                     procedure Treat_Param
                       (Formal : Entity_Id; Actual : Node_Id);
                     --  Get the parameters written in the call

                     procedure Treat_Param
                       (Formal : Entity_Id; Actual : Node_Id)
                     is
                        Var : Entity_Id;
                        Id  : Flow_Id;
                     begin
                        if Ekind (Formal) in E_Out_Parameter
                                           | E_In_Out_Parameter
                        then
                           Var := SPARK_Atree.Get_Enclosing_Object (Actual);
                           Id := Direct_Mapping_Id (Var);

                           --  Include the actual in the variables written in
                           --  the call.

                           Write_Vars.Include (Id);

                           --  Store the mapping formal->actual for possibly
                           --  removing the actual when the formal is mentioned
                           --  in the postcondition.

                           Formal_To_Actual.Insert
                             (Direct_Mapping_Id (Formal), Id);

                           --  Store the mapping actual->formal for expressing
                           --  the explanation in terms of formal parameters
                           --  missing from the postcondition. We use Include
                           --  instead of Insert here as the same actual could
                           --  correspond to multiple formals.

                           Actual_To_Formal.Include
                             (Id, Direct_Mapping_Id (Formal));
                        end if;
                     end Treat_Param;

                     procedure Iterate_Call is new
                       SPARK_Atree.Iterate_Call_Parameters (Treat_Param);

                     Proc : constant Entity_Id :=
                       SPARK_Atree.Get_Called_Entity (Stmt);

                  begin
                     --  Get the variables written in the call, both global
                     --  variables and parameters.

                     Get_Proof_Globals (Subprogram      => Proc,
                                        Reads           => Ignore_Vars,
                                        Writes          => Write_Vars,
                                        Erase_Constants => True,
                                        Scop            =>
                                          Get_Flow_Scope (Stmt));

                     Iterate_Call (Stmt);

                     --  Retrieve those variables mentioned in a postcondition

                     Info_Vars.Clear;
                     Pragmas := Get_Pre_Post (Proc, Pragma_Postcondition);
                     for Expr of Pragmas loop
                        Info_Vars.Union (Get_Variables_From_Expr
                                          (Expr, N, Formal_To_Actual));
                     end loop;

                     --  Compute variables that are both relevant for
                     --  proving the property and written in the call with
                     --  no information on the updated value.

                     Vars := Check_Vars and (Write_Vars - Info_Vars);

                     --  These variables are a possible explanation for the
                     --  proof failure.

                     if not Vars.Is_Empty then
                        Expl := Explain_Variables (Vars, Actual_To_Formal);

                        if Pragmas.Is_Empty then
                           Expl := "call "
                             & Get_Line_Number (N, Sloc (Stmt))
                             & " should mention " & Expl
                             & " in a postcondition";
                        else
                           Expl := "postcondition of call "
                             & Get_Line_Number (N, Sloc (Stmt))
                             & " should mention " & Expl;
                        end if;

                        return To_String (Expl);

                     --  Otherwise, continue the search only for the variables
                     --  that are not modified in the call.

                     else
                        Check_Vars.Difference (Write_Vars);
                     end if;
                  end;

               when N_Loop_Statement =>

                  if not Is_Selected_For_Loop_Unrolling (Stmt) then

                     --  Get the variables written in the loop

                     Write_Vars :=
                       Get_Loop_Writes (Entity (Identifier (Stmt)));
                     Pragmas :=
                       Gnat2Why.Expr.Loops.Get_Loop_Invariant (Stmt);

                     --  Compute those variables mentioned in the loop test.
                     --  Even if the loop test is not added as loop invariant,
                     --  this information may be available to prove the
                     --  property.

                     Info_Vars.Clear;

                     declare
                        Cond_Or_Var : constant Node_Or_Entity_Id :=
                          Get_Loop_Condition_Or_Variable (Stmt);
                        Id          : Flow_Id;
                     begin
                        case Nkind (Cond_Or_Var) is
                           when N_Empty =>
                              null;

                           --  The loop variable in a FOR loop is defined
                           --  by the loop, so there is no need to continue
                           --  tracking it past the loop. Remove it from
                           --  Check_Vars.

                           when N_Entity =>
                              Id := Direct_Mapping_Id (Cond_Or_Var);
                              Check_Vars.Exclude (Id);

                           --  The condition in a WHILE loop is simply
                           --  providing information on these variables
                           --  for this loop. Add them from Info_Vars.

                           when others =>
                              Info_Vars :=
                                Get_Variables_From_Expr (Cond_Or_Var, N);
                        end case;
                     end;

                     --  Retrieve those variables mentioned in a loop invariant

                     for Prag of Pragmas loop
                        declare
                           Expr : constant Node_Id :=
                             Expression (Next (First
                               (Pragma_Argument_Associations (Prag))));
                        begin
                           Info_Vars.Union (Get_Variables_From_Expr (Expr, N));
                        end;
                     end loop;

                     --  Compute variables that are both relevant for
                     --  proving the property and written in the loop with
                     --  no information on the updated value.

                     Vars := Check_Vars and (Write_Vars - Info_Vars);

                     --  These variables are a possible explanation for the
                     --  proof failure.

                     if not Vars.Is_Empty then
                        Expl := Explain_Variables (Vars);

                        if Pragmas.Is_Empty then
                           Expl := "loop "
                             & Get_Line_Number (N, Sloc (Stmt))
                             & " should mention " & Expl
                             & " in a loop invariant";
                        else
                           Expl := "loop invariant "
                             & Get_Line_Number
                                 (N, Sloc (Pragmas.First_Element))
                             & " should mention " & Expl;
                        end if;

                        return To_String (Expl);

                     --  Otherwise, continue the search only if all the
                     --  variables involved in the check are not modified in
                     --  the loop. Otherwise, it's likely that the information
                     --  provided in a loop invariant is either insufficient
                     --  or that the problem lies with prover capabilities. On
                     --  both cases, the explanation does not lie beyond the
                     --  loop itself.

                     elsif Check_Vars.Overlap (Write_Vars) then
                        return "";
                     end if;
                  end if;

               when N_Subprogram_Body
                  | N_Subprogram_Declaration
               =>
                  declare
                     Proc : constant Entity_Id :=
                       SPARK_Atree.Unique_Defining_Entity (Stmt);
                     Out_Vars : Flow_Id_Sets.Set;

                  begin
                     --  A subprogram declaration is the explaining node
                     --  for checks that happen in the precondition or
                     --  postcondition attached to this subprogram. Check
                     --  whether we are in the case, otherwise continue the
                     --  search.

                     if Nkind (Stmt) = N_Subprogram_Declaration then
                        if No (Prag_N)
                          or else
                            Get_Pragma (Proc, Get_Pragma_Id (Prag_N)) /= Prag_N
                        then
                           --  Retrieve the next explanation node to continue
                           --  the search.

                           Stmt := Get_Previous_Explain_Node (Stmt);

                           goto SEARCH;
                        end if;
                     end if;

                     --  If we're looking for an explanation for a check inside
                     --  a postcondition attached to that subprogram, restart
                     --  the search from the last statement of the subprogram
                     --  body.

                     if not Restarted_Search
                       and then Present (Prag_N)
                       and then Get_Pragma_Id (Prag_N) in
                                  Pragma_Post
                                | Pragma_Postcondition
                                | Pragma_Post_Class
                                | Pragma_Refined_Post
                     then
                        declare
                           Body_N : constant Node_Id := Get_Body (Proc);
                        begin
                           if Present (Body_N) then
                              Stmt := Last (Statements
                                        (Handled_Statement_Sequence (Body_N)));

                              --  Retrieve the next explanation node to restart
                              --  the search.

                              if Nkind (Stmt) not in Explain_Node_Kind then
                                 Stmt := Get_Previous_Explain_Node (Stmt);
                              end if;

                              Restarted_Search := True;
                              goto SEARCH;
                           end if;
                        end;
                     end if;

                     --  Report the missing precondition on the spec of the
                     --  subprogram if any.

                     declare
                        Subp_Spec : constant Node_Id := Subprogram_Spec (Proc);
                     begin
                        if Present (Subp_Spec) then
                           Stmt := Subp_Spec;
                        end if;
                     end;

                     --  Do not try to explain unproved postcondition checks
                     --  by missing information in the precondition, as it's
                     --  unlikely the cause. In such a case, stop the search
                     --  for an explanation.

                     if Tag in VC_Postcondition
                             | VC_Refined_Post
                             | VC_Contract_Case
                     then
                        return "";
                     end if;

                     --  For a check inside a postcondition, only explain
                     --  it by missing information in the precondition if
                     --  the corresponding node does not possibly refer
                     --  to post-state. Otherwise, stop the search for
                     --  an explanation.

                     if Present (Prag_N)
                       and then Get_Pragma_Id (Prag_N) in
                                  Pragma_Post
                                | Pragma_Postcondition
                                | Pragma_Post_Class
                                | Pragma_Refined_Post
                       and then Has_Post_State (N)
                     then
                        return "";
                     end if;

                     --  Get the variables read in the subprogram, both global
                     --  variables and parameters.

                     Get_Proof_Globals (Subprogram      => Proc,
                                        Reads           => Read_Vars,
                                        Writes          => Ignore_Vars,
                                        Erase_Constants => True,
                                        Scop            =>
                                          (Ent => Proc, Part => Body_Part));

                     --  Include the formal in the variables read/written in
                     --  the subprogram.

                     declare
                        Formal : Entity_Id := First_Formal (Proc);
                        Id     : Flow_Id;
                     begin
                        while Present (Formal) loop
                           Id := Direct_Mapping_Id (Formal);

                           if Ekind (Formal) in E_In_Parameter
                                              | E_In_Out_Parameter
                           then
                              --  Include the formal in the variables read in
                              --  the subprogram.
                              Read_Vars.Include (Id);

                           --  Only keep in Out_Vars output formals of
                           --  unconstrained array/record type whose
                           --  bounds/discriminants are passed as inputs.

                           elsif not Is_Constrained (Etype (Formal))
                             and then (Is_Array_Type (Etype (Formal))
                                         or else
                                       Has_Discriminants (Etype (Formal)))
                           then
                              Out_Vars.Include (Id);
                           end if;

                           Next_Formal (Formal);
                        end loop;
                     end;

                     --  Retrieve those variables mentioned in a precondition

                     Info_Vars.Clear;
                     Pragmas := Get_Pre_Post (Proc, Pragma_Precondition);
                     for Expr of Pragmas loop
                        Info_Vars.Union (Get_Variables_From_Expr (Expr, N));
                     end loop;

                     --  Compute variables that are both relevant for proving
                     --  the property and read in the subprogram with no
                     --  information on the input value.

                     Vars := Check_Vars and (Read_Vars - Info_Vars);

                     --  Compute output variables that are both relevant for
                     --  proving the property and whose bounds/discriminants
                     --  are possibly read in the subprogram with no
                     --  information on the input value.

                     Out_Vars := Check_Vars and (Out_Vars - Info_Vars);

                     --  These variables are a possible explanation for the
                     --  proof failure.

                     if not Vars.Is_Empty then
                        Expl := Explain_Variables (Vars);

                        if Is_Predicate_Function (Proc) then
                           Expl := "predicate "
                             & Get_Line_Number (N, Sloc (Stmt))
                             & " should mention " & Expl
                             & " in a guard G as in (if G then Condition)";

                        elsif Pragmas.Is_Empty then
                           Expl := "subprogram "
                             & Get_Line_Number (N, Sloc (Stmt))
                             & " should mention " & Expl
                             & " in a precondition";
                        else
                           Expl := "precondition of subprogram "
                             & Get_Line_Number (N, Sloc (Stmt))
                             & " should mention " & Expl;
                        end if;

                        return To_String (Expl);

                     elsif not Out_Vars.Is_Empty then
                        Expl := Explain_Output_Variables (Out_Vars);

                        if Pragmas.Is_Empty then
                           Expl := "subprogram "
                             & Get_Line_Number (N, Sloc (Stmt))
                             & " should mention " & Expl
                             & " in a precondition";
                        else
                           Expl := "precondition of subprogram "
                             & Get_Line_Number (N, Sloc (Stmt))
                             & " should mention " & Expl;
                        end if;

                        return To_String (Expl);

                     --  Stop the search for an explanation at the first
                     --  subprogram body, as proof is done modularly on
                     --  subprograms.

                     else
                        return "";
                     end if;
                  end;
               end case;

               Stmt := Get_Previous_Explain_Node (Stmt);

            << SEARCH >>

            end loop;

            --  No explanation was found

            return "";
         end;
      end if;
   end Get_Explanation;

   -------------------
   -- Get_Flow_JSON --
   -------------------

   function Get_Flow_JSON return JSON_Array is (Flow_Msgs);

   --------------------
   -- Get_Proof_JSON --
   --------------------

   function Get_Proof_JSON return JSON_Array is (Proof_Msgs);

   --------------------------
   -- Get_Session_Map_JSON --
   --------------------------

   function Get_Session_Map_JSON return JSON_Value is
      Value : constant JSON_Value := Create_Object;
   begin
      for Key in Session_File_Map.First_Index .. Session_File_Map.Last_Index
      loop
         Set_Field (Value,
                    Session_Dir_ID'Image (Key),
                    Session_File_Map (Key));
      end loop;
      return Value;
   end Get_Session_Map_JSON;

   -----------------------
   -- Is_Specified_Line --
   -----------------------

   function Is_Specified_Line (Slc : Source_Ptr) return Boolean is
      Result : Boolean := True;
   begin
      if Gnat2Why_Args.Limit_Line /= Null_Unbounded_String then
         declare
            File : constant String := File_Name (Slc);
            Line : constant Physical_Line_Number :=
              Get_Physical_Line_Number (Slc);
         begin
            Result := To_String (Gnat2Why_Args.Limit_Line) =
              File & ":" & Image (Value => Positive (Line), Min_Width => 1);
         end;
      end if;

      if Gnat2Why_Args.Limit_Region /= Null_Unbounded_String then
         declare
            File            : constant String := File_Name (Slc);
            Line            : constant Physical_Line_Number :=
              Get_Physical_Line_Number (Slc);
            Fst_Colon_Index : constant Natural :=
              Index (Source  => Limit_Region,
                     Pattern => ":");
            Snd_Colon_Index : constant Natural :=
              Index (Source  => Limit_Region,
                     Pattern => ":",
                     From => Fst_Colon_Index + 1);
         begin
            Result := Result
              and then File = Slice (Limit_Region, 1, Fst_Colon_Index - 1)
              and then Positive (Line) in
                  Integer'Value (Slice (Limit_Region,
                                        Fst_Colon_Index + 1,
                                        Snd_Colon_Index - 1))
                  .. Integer'Value (Slice (Limit_Region,
                                           Snd_Colon_Index + 1,
                                           Length (Limit_Region)));
         end;
      end if;

      return Result;
   end Is_Specified_Line;

   ----------------------------
   -- Msg_Severity_To_String --
   ----------------------------

   function Msg_Severity_To_String (Severity : Msg_Severity) return String is
     (case Severity is
         when Error_Kind        => "error",
         when Warning_Kind      => "warning",
         when Info_Kind         => "info",
         when High_Check_Kind   => "high",
         when Medium_Check_Kind => "medium",
         when Low_Check_Kind    => "low");

   ------------------
   -- Add_Json_Msg --
   ------------------

   procedure Add_Json_Msg
     (Suppr      : String_Id;
      Tag        : String;
      Severity   : Msg_Severity;
      Slc        : Source_Ptr;
      Msg_List   : in out GNATCOLL.JSON.JSON_Array;
      E          : Entity_Id;
      Msg_Id     : Message_Id;
      How_Proved : Prover_Category;
      Tracefile  : String := "";
      Cntexmp    : Cntexample_File_Maps.Map := Cntexample_File_Maps.Empty_Map;
      Check_Tree : JSON_Value;
      SD_Id      : Session_Dir_Base_ID := No_Session_Dir;
      VC_File    : String := "";
      VC_Loc     : Source_Ptr := No_Location;
      Stats      : Prover_Stat_Maps.Map := Prover_Stat_Maps.Empty_Map;
      Editor_Cmd : String := "")
   is
      Value : constant JSON_Value := Create_Object;
      File  : constant String     := File_Name (Slc);
      Line  : constant Natural    := Natural (Get_Logical_Line_Number (Slc));
      Col   : constant Natural    := Natural (Get_Column_Number (Slc));
   begin

      Set_Field (Value, "file", File);
      Set_Field (Value, "line", Line);
      Set_Field (Value, "col", Col);

      if Suppr /= No_String then
         declare
            Len           : constant Natural :=
              Natural (String_Length (Suppr));
            Reason_String : String (1 .. Len);
         begin
            String_To_Name_Buffer (Suppr);
            Reason_String := Name_Buffer (1 .. Len);
            Set_Field (Value, "suppressed", Reason_String);
         end;
      end if;

      Set_Field (Value, "rule", Tag);
      Set_Field (Value, "severity", Msg_Severity_To_String (Severity));
      Set_Field (Value, "entity", To_JSON (Entity_To_Subp_Assumption (E)));
      Set_Field (Value, "check_tree", Check_Tree);

      if VC_Loc /= No_Location then
         declare
            VC_File : constant String  := File_Name (VC_Loc);
            VC_Line : constant Natural :=
                         Natural (Get_Logical_Line_Number (VC_Loc));
            VC_Col  : constant Natural :=
                         Natural (Get_Column_Number (VC_Loc));
         begin
            --  Note that vc_file already exists
            Set_Field (Value, "check_file", VC_File);
            Set_Field (Value, "check_line", VC_Line);
            Set_Field (Value, "check_col", VC_Col);
         end;
      end if;

      if Tracefile /= "" then
         Set_Field (Value, "tracefile", Tracefile);
      end if;

      if not Cntexmp.Is_Empty then
         Set_Field (Value, "cntexmp", To_JSON (Cntexmp));
      end if;

      if VC_File /= "" then
         Set_Field (Value, "vc_file", VC_File);
      end if;

      if Editor_Cmd /= "" then
         Set_Field (Value, "editor_cmd", Editor_Cmd);
      end if;

      if Msg_Id /= No_Message_Id then
         Set_Field (Value, "msg_id", Integer (Msg_Id));
      end if;

      if SD_Id /= No_Session_Dir then
         Set_Field (Value, "session_dir", Integer (SD_Id));
      end if;

      Set_Field (Value, "how_proved", To_JSON (How_Proved));

      if not Stats.Is_Empty then
         Set_Field (Value, "stats", To_JSON (Stats));
      end if;

      Append (Msg_List, Value);
   end Add_Json_Msg;

   -----------------------
   -- Print_Regular_Msg --
   -----------------------

   function Print_Regular_Msg
     (Msg          : String;
      Slc          : Source_Ptr;
      Severity     : Msg_Severity;
      Continuation : Boolean := False)
      return Message_Id
   is
      Id         : constant Message_Id := Message_Id_Counter;
      Prefix     : constant String :=
        (if Continuation then "\" else "") &
        (case Severity is
            when Info_Kind         => "info: ",
            when Low_Check_Kind    => "low: ",
            when Medium_Check_Kind => "medium: ",
            when High_Check_Kind   => "high: ",
            when Warning_Kind      => "?",
            when Error_Kind        => "");
      Actual_Msg : constant String :=
        Prefix & Escape (Msg) & "!!" &
        (if Ide_Mode
         then "'['#" & Image (Integer (Id), 1) & "']"
         else "");
   begin
      Message_Id_Counter := Message_Id_Counter + 1;
      Error_Msg (Actual_Msg, Slc);
      return Id;
   end Print_Regular_Msg;

   ---------------------------
   -- Register_Session_File --
   ---------------------------

   function Register_Session_Dir (S : String) return Session_Dir_ID is
   begin
      Session_File_Map.Append (S);
      return Session_File_Map.Last_Index;
   end Register_Session_Dir;

   ----------------
   -- Substitute --
   ----------------

   function Substitute
     (S    : Unbounded_String;
      F    : Flow_Id;
      Flag : Source_Ptr)
      return Unbounded_String
   is
      R      : Unbounded_String := Null_Unbounded_String;
      Do_Sub : Boolean          := True;
      Quote  : Boolean;

      procedure Append_Quote;
      --  Append a quote on R if Quote is True

      ------------------
      -- Append_Quote --
      ------------------

      procedure Append_Quote is
      begin
         if Quote then
            Append (R, """");
         end if;
      end Append_Quote;

   --  Start of processing for Substitute

   begin
      for Index in Positive range 1 .. Length (S) loop
         if Do_Sub then
            case Element (S, Index) is
            when '&' | '#' | '%' =>
               Quote := Element (S, Index) in '&' | '#';

               case F.Kind is
               when Null_Value =>
                  raise Program_Error;

               when Synthetic_Null_Export =>
                  Append_Quote;
                  Append (R, "null");

               when Direct_Mapping | Record_Field =>
                  if Is_Private_Part (F) then
                     Append (R, "private part of ");
                     Append_Quote;
                     Append (R, Flow_Id_To_String
                               (F'Update (Facet => Normal_Part)));
                  elsif Is_Extension (F) then
                     Append (R, "extension of ");
                     Append_Quote;
                     Append (R, Flow_Id_To_String
                               (F'Update (Facet => Normal_Part)));
                  elsif Is_Bound (F) then
                     Append (R, "bounds of ");
                     Append_Quote;
                     Append (R, Flow_Id_To_String
                               (F'Update (Facet => Normal_Part)));
                  elsif Nkind (Get_Direct_Mapping_Id (F)) in N_Entity
                    and then Ekind (Get_Direct_Mapping_Id (F)) = E_Constant
                  then
                     declare
                        Var : constant Entity_Id := Get_Direct_Mapping_Id (F);

                     begin
                        if Nkind (Original_Node (Parent (Var))) =
                          N_Object_Renaming_Declaration
                        then
                           Append (R, "renaming of a function call ");
                        else
                           Append (R, "constant with");
                           if not Has_Variable_Input (Var) then
                              Append (R, "out");
                           end if;
                           Append (R, " variable input ");
                        end if;
                     end;
                     Append_Quote;
                     Append (R, Flow_Id_To_String (F));
                  elsif Nkind (Get_Direct_Mapping_Id (F)) =
                     N_Defining_Operator_Symbol
                  then
                     Append (R, "overriding operator ");
                     Append_Quote;
                     Append (R, Flow_Id_To_String (F));
                  elsif Is_Constituent (F) then
                     declare
                        Constituent_Id : constant Entity_Id :=
                          Get_Direct_Mapping_Id (F);

                        State_Id : constant Entity_Id :=
                          Encapsulating_State (Constituent_Id);
                        --  Encapsulating state of the constituent

                        Constituent_Scope : constant Entity_Id :=
                          Scope (Constituent_Id);
                        --  Immediate scope of the constituent

                        State_Scope : constant Entity_Id := Scope (State_Id);
                        --  Immediate scope of the abstract state

                     begin
                        Append_Quote;
                        Append (R, Flow_Id_To_String (F));
                        Append_Quote;
                        Append (R, " constituent of ");
                        Append_Quote;

                        --  If the scope of the constituent is different from
                        --  the scope of its abstract state then we want to
                        --  prefix the name of the abstract state with its
                        --  immediate scope.

                        if State_Scope /= Constituent_Scope then
                           Get_Name_String (Chars (State_Scope));
                           Adjust_Name_Case (Sloc (State_Scope));
                           Append (R, Name_Buffer (1 .. Name_Len) & ".");
                        end if;

                        --  We append the abstract state. Note that we are not
                        --  using Flow_Id_To_String because of the special
                        --  handling above. In fact, we only add a prefix when
                        --  the immediate scope of the constituent is different
                        --  than the immediate scope of the abstract state.

                        Get_Name_String (Chars (State_Id));
                        Adjust_Name_Case (Sloc (State_Id));
                        Append (R, Name_Buffer (1 .. Name_Len));
                     end;
                  else
                     Append_Quote;
                     Append (R, Flow_Id_To_String (F));
                  end if;

               when Magic_String =>
                  --  ??? we may want to use __gnat_decode() here instead
                  Append_Quote;
                  declare
                     F_Name_String : constant String :=
                       Strip_Child_Prefixes (To_String (F.Name));

                  begin
                     if F_Name_String = "__HEAP" then
                        Append (R, "memory accessed through objects of " &
                                   "access type");
                     else
                        declare
                           Index : Positive := F_Name_String'First;

                        begin
                           --  Replace __ with . in the magic string
                           while Index <= F_Name_String'Last loop
                              case F_Name_String (Index) is
                              when '_' =>
                                 if Index < F_Name_String'Last
                                   and then F_Name_String (Index + 1) = '_'
                                 then
                                    Append (R, ".");
                                    Index := Index + 2;
                                 else
                                    Append (R, '_');
                                    Index := Index + 1;
                                 end if;

                              when others =>
                                 Append (R, F_Name_String (Index));
                                 Index := Index + 1;
                              end case;
                           end loop;
                        end;
                     end if;
                  end;
               end case;

               Append_Quote;

               if Element (S, Index) = '#' then
                  case F.Kind is
                  when Direct_Mapping | Record_Field =>
                     declare
                        N : constant Node_Id := Get_Direct_Mapping_Id (F);

                     begin
                        Msglen := 0;
                        Set_Msg_Insertion_Line_Number (Sloc (N), Flag);
                        Append (R, " ");
                        Append (R, Msg_Buffer (1 .. Msglen));
                     end;
                  when others =>
                     --  Can't really add source information for stuff that
                     --  doesn't come from the tree.
                     null;
                  end case;
               end if;

               Do_Sub := False;

            when '@' =>
               declare
                  N : constant Node_Id := Get_Direct_Mapping_Id (F);

               begin
                  Msglen := 0;
                  Set_Msg_Insertion_Line_Number (Sloc (N), Flag);
                  Append (R, Msg_Buffer (1 .. Msglen));
               end;

            when others =>
               Append (R, Element (S, Index));
            end case;
         else
            Append (R, Element (S, Index));
         end if;
      end loop;

      return R;
   end Substitute;

   ---------------------------
   -- Warning_Is_Suppressed --
   ---------------------------

   function Warning_Is_Suppressed
     (N   : Node_Id;
      Msg : String;
      F1  : Flow_Id := Null_Flow_Id;
      F2  : Flow_Id := Null_Flow_Id;
      F3  : Flow_Id := Null_Flow_Id)
      return String_Id
   is

      function Warning_Disabled_For_Entity return Boolean;
      --  Returns True if either of N, F1, F2 correspond to an entity that
      --  Has_Warnings_Off.

      ---------------------------------
      -- Warning_Disabled_For_Entity --
      ---------------------------------

      function Warning_Disabled_For_Entity return Boolean is

         function Is_Entity_And_Has_Warnings_Off
           (N : Node_Or_Entity_Id) return Boolean
         is
           ((Nkind (N) in N_Has_Entity
               and then Present (Entity (N))
               and then Has_Warnings_Off (Entity (N)))
               or else
            (Nkind (N) in N_Entity
               and then Has_Warnings_Off (N)));
         --  Returns True if N is an entity and Has_Warnings_Off (N)

         function Is_Entity_And_Has_Warnings_Off
           (F : Flow_Id) return Boolean
         is
           (F.Kind in Direct_Mapping | Record_Field
              and then
            Is_Entity_And_Has_Warnings_Off (Get_Direct_Mapping_Id (F)));

      begin
         --  ??? if Fn is not present, then there is no point to check F(n+1)
         return Is_Entity_And_Has_Warnings_Off (N)
           or else Is_Entity_And_Has_Warnings_Off (F1)
           or else Is_Entity_And_Has_Warnings_Off (F2)
           or else Is_Entity_And_Has_Warnings_Off (F3);
      end Warning_Disabled_For_Entity;

      Suppr_Reason : String_Id := Warnings_Suppressed (Sloc (N));

   --  Start of processing for Warning_Is_Suppressed

   begin
      if Suppr_Reason = No_String then
         Suppr_Reason :=
           Warning_Specifically_Suppressed
             (Loc => Sloc (N),
              Msg => Msg'Unrestricted_Access);

         if Suppr_Reason = No_String
           and then Warning_Disabled_For_Entity
         then
            Suppr_Reason := Null_String_Id;
         end if;
      end if;
      return Suppr_Reason;
   end Warning_Is_Suppressed;

end Flow_Error_Messages;
