------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                  F L O W _ E R R O R _ M E S S A G E S                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2013-2014, Altran UK Limited              --
--                  Copyright (C) 2013-2014, AdaCore                        --
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

with Ada.Containers.Hashed_Sets;
with Ada.Strings.Unbounded.Hash;

with Atree;                use Atree;
with Einfo;                use Einfo;
with Errout;               use Errout;
with Erroutc;              use Erroutc;
with Namet;                use Namet;
with Sinfo;                use Sinfo;
with Sinput;               use Sinput;
with Stringt;              use Stringt;

with Assumption_Types;     use Assumption_Types;
with Gnat2Why.Annotate;    use Gnat2Why.Annotate;
with Gnat2Why.Assumptions; use Gnat2Why.Assumptions;
with Gnat2Why.Nodes;       use Gnat2Why.Nodes;
with Gnat2Why_Args;        use Gnat2Why_Args;
with SPARK_Util;           use SPARK_Util;
with String_Utils;         use String_Utils;

package body Flow_Error_Messages is

   package Msgs_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Unbounded_String,
      Hash                => Ada.Strings.Unbounded.Hash,
      Equivalent_Elements => "=",
      "="                 => "=");

   Flow_Msgs_Set : Msgs_Sets.Set;
   --  This set will contain flow related messages. It is used so as
   --  to not emit duplicate messages.

   function Msg_Kind_To_String (Kind : Msg_Kind) return String;
   --  transform the msg kind into a string, for the JSON output

   type Message_Id is new Integer;
   --  type used to identify a message issued by gnat2why

   function Compute_Message
     (Msg  : String;
      N    : Node_Id;
      F1   : Flow_Id := Null_Flow_Id;
      F2   : Flow_Id := Null_Flow_Id)
      return String;
   --  This function does:
   --    * add more precise location for generics and inlining
   --    * substitute flow nodes

   function Compute_Sloc
     (N           : Node_Id;
      Place_First : Boolean := False)
      return Source_Ptr;

   procedure Add_Json_Msg
     (Suppr       : String_Id;
      Tag         : String;
      Kind        : Msg_Kind;
      Slc         : Source_Ptr;
      Msg_List    : in out GNATCOLL.JSON.JSON_Array;
      E           : Entity_Id;
      Msg_Id      : Message_Id;
      Tracefile   : String := "";
      VC_File     : String := "";
      Editor_Cmd  : String := "");

   function Warning_Is_Suppressed
     (N   : Node_Id;
      Msg : String;
      F1   : Flow_Id := Null_Flow_Id;
      F2   : Flow_Id := Null_Flow_Id)
     return String_Id;
   --  Check if the warning for the given node, message and flow Id is
   --  suppressed. If the function returns No_String, the warning is not
   --  suppressed. If it returns Null_String_Id the warning is suppressed,
   --  but no reason has been given. Otherwise, the String_Id of the reason
   --  is provided.

   function Print_Regular_Msg
     (Msg  : String;
      Slc  : Source_Ptr;
      Kind : Msg_Kind) return Message_Id;
   --  print a regular error, warning or info message using the frontend
   --  mechanism. return an Id which can be used to identify this message.

   Flow_Msgs : GNATCOLL.JSON.JSON_Array;
   --  This will hold all of the emitted flow messages in JSON format

   Proof_Msgs : GNATCOLL.JSON.JSON_Array;

   use type Ada.Containers.Count_Type;
   use type Flow_Graphs.Vertex_Id;
   use type Flow_Id_Sets.Set;

   function Escape (S : String) return String;
   --  Escape any special characters used in the error message (for
   --  example transforms "=>" into "='>" as > is a special insertion
   --  character.

   function Substitute
     (S    : Unbounded_String;
      F    : Flow_Id;
      Flag : Source_Ptr)
      return Unbounded_String;
   --  Find the first '&' or '%' and substitute with the given flow id,
   --  with or without enclosing quotes respectively. Alternatively, '#'
   --  works like '&', but is followed by a line reference.

   File_Counter : Integer := 0;
   Message_Id_Counter : Message_Id := 0;
   No_Message_Id : constant Message_Id := -1;

   ---------------------
   -- Compute_Message --
   ---------------------

   function Compute_Message
     (Msg  : String;
      N    : Node_Id;
      F1   : Flow_Id := Null_Flow_Id;
      F2   : Flow_Id := Null_Flow_Id)
      return String is
      M : Unbounded_String := Null_Unbounded_String;
   begin
      Append (M, Msg);
      if Present (F1) then
         M := Substitute (M, F1, Sloc (N));
      end if;
      if Present (F2) then
         M := Substitute (M, F2, Sloc (N));
      end if;

      if Instantiation_Location (Sloc (N)) /= No_Location then

         --  If we are dealing with an instantiation of a generic we change
         --  the message to point at the implementation of the generic and we
         --  mention where the generic is instantiated.

         declare
            Tmp     : Source_Ptr := Sloc (First_Node (N));
            File    : Unbounded_String;
            Line    : Physical_Line_Number;
            Context : Unbounded_String;
         begin
            loop
               exit when Instantiation_Location (Tmp) = No_Location;
               if Comes_From_Inlined_Body (Tmp) then
                  Context := To_Unbounded_String (", in call inlined at ");
               else
                  Context := To_Unbounded_String (", in instantiation at ");
               end if;

               Tmp := Instantiation_Location (Tmp);
               File := To_Unbounded_String (File_Name (Tmp));
               Line := Get_Physical_Line_Number (Tmp);
               Append (M, To_String (Context) &
                         To_String (File) & ":" & Int_Image (Integer (Line)));
            end loop;
         end;
      end if;
      return To_String (M);
   end Compute_Message;

   function Compute_Sloc
     (N           : Node_Id;
      Place_First : Boolean := False) return Source_Ptr
   is
      Slc : Source_Ptr;
   begin
      if Instantiation_Location (Sloc (N)) /= No_Location then
         --  If we are dealing with an instantiation of a generic we change
         --  the message to point at the implementation of the generic and we
         --  mention where the generic is instantiated.
         Slc := Original_Location (Sloc (N));

      elsif Place_First then
         Slc := First_Sloc (N);
      else
         Slc := Sloc (N);
      end if;
      return Slc;
   end Compute_Sloc;

   --------------------
   -- Error_Msg_Flow --
   --------------------

   procedure Error_Msg_Flow
     (E          : Entity_Id;
      Msg        : String;
      Kind       : Msg_Kind;
      N          : Node_Id;
      Suppressed : out Boolean;
      F1         : Flow_Id   := Null_Flow_Id;
      F2         : Flow_Id   := Null_Flow_Id;
      Tag        : String    := "";
      SRM_Ref    : String    := "";
      Tracefile  : String    := "")
   is
      Msg2    : constant String :=
        (if SRM_Ref'Length > 0 then Msg & " (SPARK RM " & SRM_Ref & ")"
         else Msg);
      Msg3    : constant String := Compute_Message (Msg2, N, F1, F2);
      Suppr   : String_Id := No_String;
      Slc     : constant Source_Ptr := Compute_Sloc (N);
      Msg_Id  : Message_Id := No_Message_Id;
      Unb_Msg : constant Unbounded_String :=
        To_Unbounded_String (Msg3) &
        To_Unbounded_String (Source_Ptr'Image (Slc)) &
          To_Unbounded_String (Msg_Kind_To_String (Kind));

      function Is_Specified_Line return Boolean;
      --  Returns True if command line argument "--limit-line" was not
      --  given, or if the the message currently being processed is to
      --  be emitted on the line specified by the "--limit-line"
      --  argument.

      -----------------------
      -- Is_Specified_Line --
      -----------------------

      function Is_Specified_Line return Boolean is
         Loc  : constant Source_Ptr :=
           Translate_Location (Sloc (N));
         File : constant String := File_Name (Loc);
         Line : constant Physical_Line_Number :=
           Get_Physical_Line_Number (Loc);
      begin
         return Gnat2Why_Args.Limit_Line = Null_Unbounded_String
           or else File & ":" & Int_Image (Integer (Line)) =
                     To_String (Gnat2Why_Args.Limit_Line);
      end Is_Specified_Line;

   begin
      --  If the message we are about to emit has already been emitted
      --  in the past then do nothing.

      if Flow_Msgs_Set.Contains (Unb_Msg) then
         Suppressed := True;
      else
         Flow_Msgs_Set.Insert (Unb_Msg);

         if Kind = Warning_Kind then
            Suppr := Warning_Is_Suppressed (N, Msg3, F1, F2);
         elsif Kind in Check_Kind then
            declare
               Is_Annot : Boolean;
               Info     : Annotated_Range;
            begin
               Check_Is_Annotated (N, Msg3, Is_Annot, Info);
               if Is_Annot then
                  Suppr := Info.Reason;
               end if;
            end;
         end if;
         Suppressed := Suppr /= No_String;

         --  Print the message except when it's suppressed.
         --  Additionally, if command line argument "--limit-line" was
         --  given, only issue the warning if it is to be emitted on
         --  the specified line (errors are emitted anyway).

         if not Suppressed and then Is_Specified_Line then
            Msg_Id := Print_Regular_Msg (Msg3, Slc, Kind);
         end if;

         Add_Json_Msg
           (Suppr     => Suppr,
            Tag       => Tag,
            Kind      => Kind,
            Slc       => Slc,
            Msg_List  => Flow_Msgs,
            E         => E,
            Tracefile => Tracefile,
            Msg_Id    => Msg_Id);

         --  Set the error flag if we have an error message. Note that
         --  warnings do not count as errors here, they should not prevent
         --  us going to proof. The errout mechanism already deals with the
         --  warnings-as-errors handling for the whole unit.

         if Kind = Error_Kind then
            Found_Flow_Error := True;
         end if;
      end if;
   end Error_Msg_Flow;

   procedure Error_Msg_Flow
     (FA        : in out Flow_Analysis_Graphs;
      Msg       : String;
      Kind      : Msg_Kind;
      N         : Node_Id;
      F1        : Flow_Id               := Null_Flow_Id;
      F2        : Flow_Id               := Null_Flow_Id;
      Tag       : String                := "";
      SRM_Ref   : String                := "";
      Tracefile : String                := "";
      Vertex    : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex)
   is
      E       : Entity_Id;
      Img     : constant String := Natural'Image
        (FA.CFG.Vertex_To_Natural (Vertex));
      Tmp     : constant String :=
        (if Gnat2Why_Args.Flow_Advanced_Debug and then
           Vertex /= Flow_Graphs.Null_Vertex
         then Msg & " <" & Img (2 .. Img'Last) & ">"
         else Msg);
      Suppressed : Boolean;
   begin
      case FA.Kind is
         when E_Subprogram_Body | E_Package =>
            E := FA.Analyzed_Entity;
         when E_Package_Body =>
            E := Spec_Entity (FA.Analyzed_Entity);
      end case;

      Error_Msg_Flow (E          => E,
                      Msg        => Tmp,
                      Kind       => Kind,
                      N          => N,
                      Suppressed => Suppressed,
                      F1         => F1,
                      F2         => F2,
                      Tag        => Tag,
                      SRM_Ref    => SRM_Ref,
                      Tracefile  => Tracefile);

      --  Set the No_Errors_Or_Warnings flag to False for this
      --  entity if we are dealing with anything but a suppressed
      --  warning.

      if not Suppressed then
         FA.No_Errors_Or_Warnings := False;
      end if;
   end Error_Msg_Flow;

   ---------------------
   -- Error_Msg_Proof --
   ---------------------

   procedure Error_Msg_Proof
     (N           : Node_Id;
      Msg         : String;
      Is_Proved   : Boolean;
      Tag         : String;
      Tracefile   : String;
      VC_File     : String;
      Editor_Cmd  : String;
      E           : Entity_Id;
      Place_First : Boolean) is
      Kind   : constant Msg_Kind :=
        (if Is_Proved then Info_Kind else Medium_Check_Kind);
      Msg2   : constant String :=
        Compute_Message (Msg, N);
      Suppr  : String_Id := No_String;
      Slc    : constant Source_Ptr := Compute_Sloc (N, Place_First);
      Msg_Id : Message_Id := No_Message_Id;
   begin
      case Kind is
         when Check_Kind =>
            declare
               Is_Annot : Boolean;
               Info     : Annotated_Range;
            begin
               Check_Is_Annotated (N, Msg, Is_Annot, Info);
               if Is_Annot then
                  Suppr := Info.Reason;
               else
                  Msg_Id := Print_Regular_Msg (Msg2, Slc, Kind);
               end if;
            end;
         when Info_Kind =>
            if Report_Mode /= GPR_Fail then
               Msg_Id := Print_Regular_Msg (Msg2, Slc, Kind);
            end if;
         when Error_Kind | Warning_Kind =>
            --  cannot happen
            null;
      end case;

      Add_Json_Msg
        (Suppr      => Suppr,
         Tag        => Tag,
         Kind       => Kind,
         Slc        => Slc,
         Msg_List   => Proof_Msgs,
         Msg_Id     => Msg_Id,
         E          => E,
         Tracefile  => Tracefile,
         VC_File    => VC_File,
         Editor_Cmd => Editor_Cmd);

   end Error_Msg_Proof;

   ------------
   -- Escape --
   ------------

   function Escape (S : String) return String is
      R : Unbounded_String := Null_Unbounded_String;
   begin
      for Index in S'Range loop
         if S (Index) in '%' | '$' | '{' | '*' | '&' |
           '#' | '}' | '@' | '^' | '>' |
           '!' | '?' | '<' | '`' | ''' | '\' | '|'
         then
            Append (R, "'");
         end if;

         Append (R, S (Index));
      end loop;

      return To_String (R);
   end Escape;

   ----------------------
   -- Fresh_Trace_File --
   ----------------------

   function Fresh_Trace_File return String is
      Result : constant String :=
        Unit_Name & "__flow__" & Int_Image (File_Counter) & ".trace";
   begin
      File_Counter := File_Counter + 1;
      return Result;
   end Fresh_Trace_File;

   -------------------
   -- Get_Flow_JSON --
   -------------------

   function Get_Flow_JSON return JSON_Array is (Flow_Msgs);

   --------------------
   -- Get_Proof_JSON --
   --------------------

   function Get_Proof_JSON return JSON_Array is (Proof_Msgs);

   ------------------------
   -- Msg_Kind_To_String --
   ------------------------

   function Msg_Kind_To_String (Kind : Msg_Kind) return String is
   begin
      case Kind is
         when Error_Kind =>
            return "error";
         when Warning_Kind =>
            return "warning";
         when Info_Kind =>
            return "info";
         when High_Check_Kind =>
            return "high";
         when Medium_Check_Kind =>
            return "medium";
         when Low_Check_Kind =>
            return "low";
      end case;
   end Msg_Kind_To_String;

   ------------------
   -- Add_Json_Msg --
   ------------------

   procedure Add_Json_Msg
     (Suppr       : String_Id;
      Tag         : String;
      Kind        : Msg_Kind;
      Slc         : Source_Ptr;
      Msg_List    : in out GNATCOLL.JSON.JSON_Array;
      E           : Entity_Id;
      Msg_Id      : Message_Id;
      Tracefile   : String := "";
      VC_File     : String := "";
      Editor_Cmd  : String := "") is

      Value     : constant JSON_Value := Create_Object;
      File       : constant String := File_Name (Slc);
      Line       : constant Integer :=
        Integer (Get_Logical_Line_Number (Slc));
      Col        : constant Integer := Integer (Get_Column_Number (Slc));
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
            Set_Field (Value, "message", Reason_String);
         end;
      end if;

      --  ??? pragma Warning is not very good ...

      Set_Field (Value, "rule",
                 (if Suppr /= No_String then
                     "pragma_warning"
                  else Tag));

      Set_Field (Value, "severity", Msg_Kind_To_String (Kind));
      Set_Field (Value, "entity", To_JSON (Entity_To_Subp (E)));

      if Tracefile /= "" then
         Set_Field (Value, "tracefile", Tracefile);
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

      Append (Msg_List, Value);
   end Add_Json_Msg;

   -----------------------
   -- Print_Regular_Msg --
   -----------------------

   function Print_Regular_Msg
     (Msg  : String;
      Slc  : Source_Ptr;
      Kind : Msg_Kind) return Message_Id is
      Id          : constant Message_Id := Message_Id_Counter;
      Prefix      : constant String :=
        (case Kind is
            when Info_Kind         => "info: ?",
            when Low_Check_Kind    => "low: ",
            when Medium_Check_Kind => "medium: ",
            when High_Check_Kind   => "high: ",
            when Warning_Kind      => "?",
            when Error_Kind        => "");
      Actual_Msg : constant String :=
        Prefix & Escape (Msg) & "!!" &
      (if Ide_Mode then
          "'['#" & Int_Image (Integer (Id)) & "']"
       else "");
   begin
      Message_Id_Counter := Message_Id_Counter + 1;
      Error_Msg (Actual_Msg, Slc);
      return Id;
   end Print_Regular_Msg;

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
   begin
      for Index in Positive range 1 .. Length (S) loop
         if Do_Sub and then Element (S, Index) in '&' | '#' | '%' then
            Quote := Element (S, Index) in '&' | '#';

            if Quote then
               Append (R, """");
            end if;

            case F.Kind is
               when Null_Value =>
                  raise Program_Error;

               when Synthetic_Null_Export =>
                  Append (R, "null");

               when Direct_Mapping | Record_Field =>
                  if Is_Private_Part (F) then
                     Append (R, "private part of ");
                     Append (R, Flow_Id_To_String
                               (F'Update (Facet => Normal_Part)));
                  elsif Is_Extension (F) then
                     Append (R, "extension of ");
                     Append (R, Flow_Id_To_String
                               (F'Update (Facet => Normal_Part)));
                  elsif Is_Bound (F) then
                     Append (R, "bounds of ");
                     Append (R, Flow_Id_To_String
                               (F'Update (Facet => Normal_Part)));
                  else
                     Append (R, Flow_Id_To_String (F));
                  end if;

               when Magic_String =>
                  --  ??? we may want to use __gnat_decode() here instead
                  if F.Name.all = "__HEAP" then
                     Append (R, "the heap");
                  else
                     declare
                        Index : Positive := F.Name.all'First;
                     begin
                        --  Replace __ with . in the magic string.
                        while Index <= F.Name.all'Last loop
                           case F.Name.all (Index) is
                              when '_' =>
                                 if Index < F.Name.all'Last and then
                                   F.Name.all (Index + 1) = '_'
                                 then
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
                  end if;
            end case;

            if Quote then
               Append (R, """");
            end if;

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
      F1   : Flow_Id := Null_Flow_Id;
      F2   : Flow_Id := Null_Flow_Id)
     return String_Id is

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

      begin
         if Is_Entity_And_Has_Warnings_Off (N) then
            return True;
         end if;

         if Present (F1)
           and then F1.Kind in Direct_Mapping | Record_Field
           and then Is_Entity_And_Has_Warnings_Off (Get_Direct_Mapping_Id (F1))
         then
            return True;
         end if;

         if Present (F2)
           and then F2.Kind in Direct_Mapping | Record_Field
           and then Is_Entity_And_Has_Warnings_Off (Get_Direct_Mapping_Id (F2))
         then
            return True;
         end if;

         return False;
      end Warning_Disabled_For_Entity;

      Suppr_Reason : String_Id := Warnings_Suppressed (Sloc (N));

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
