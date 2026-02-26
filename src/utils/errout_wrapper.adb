------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        E R R O U T _ W R A P P E R                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--              Copyright (C) 2014-2026, Capgemini Engineering              --
--                     Copyright (C) 2014-2026, AdaCore                     --
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
with Assumption_Types;        use Assumption_Types;
with Atree;                   use Atree;
with Einfo.Utils;             use Einfo.Utils;
with Erroutc;
with Gnat2Why_Args;
with Gnat2Why_Opts;           use Gnat2Why_Opts;
with Sinfo.Nodes;             use Sinfo.Nodes;
with Sinfo.Utils;             use Sinfo.Utils;
with Sinput;                  use Sinput;
with SPARK_Util;              use SPARK_Util;
with Stringt;                 use Stringt;
with Warnsw;                  use Warnsw;

package body Errout_Wrapper is

   Message_Id_Counter : Message_Id := 0;
   --  Counter used to generate Message_Ids

   function Escape_For_Errout (S : String) return String;
   --  Escape any special characters used in the error message (for example
   --  transforms "=>" into "='>" as > is a special insertion character. We
   --  don't escape '&' and '#' which are interpreted. We also escape capital
   --  letters.

   generic
      with procedure Locate_Message (Msg : String; First_Node : Node_Id);
   procedure Print
     (Msg           : Message;
      Kind          : Msg_Severity := Error_Kind;
      Continuations : Message_Lists.List := Message_Lists.Empty);
   --  Prepare the call to the Errout backend, e.g. Errout.Error_Msg_N.
   --  The actual call shall be made by the generic argument procedure.

   function Create_N
     (Msg           : String;
      Names         : String_Lists.List := String_Lists.Empty;
      Secondary_Loc : Source_Ptr := No_Location;
      Explain_Code  : Explain_Code_Kind := EC_None) return Message;
   --  Same as Create, but the names can be provided as a list of Strings.

   function To_JSON (M : Message) return JSON_Value;
   --  Transform message object into JSON (SARIF) message object

   function To_SARIF_Msg_Text
     (S : Unbounded_String; Contains_Placeholder : out Boolean) return String;
   --  Processes the string object to remove quoting with ''' and replacing &
   --  by SARIF indices. Set Contains_Placeholder to True if the original
   --  string contained &.

   function Node_To_Name (N : Node_Id) return String;
   --  Convert the node to a String. This is mostly a wrapper around
   --  Raw_Source_Name.

   function Add_Default_Name (Msg : Message; N : Node_Id) return Message;
   --  If the message doesn't contain any names, add the node N as a single
   --  name.

   ----------------------
   -- Add_Default_Name --
   ----------------------

   function Add_Default_Name (Msg : Message; N : Node_Id) return Message is
      Names : constant Node_Lists.List :=
        (if Present (N) and then Msg.Names.Is_Empty
         then Node_Lists.List'([N])
         else Node_Lists.List'(Msg.Names));
   begin
      return (Msg with delta Names => Names);
   end Add_Default_Name;

   ------------------
   -- Add_Json_Msg --
   ------------------

   procedure Add_Json_Msg
     (Msg_List : in out GNATCOLL.JSON.JSON_Array;
      Obj      : JSON_Result_Type;
      Msg_Id   : Message_Id := No_Message_Id)
   is
      Value : constant JSON_Value := Create_Object;
      File  : constant String := File_Name (Obj.Span.Ptr);
      Line  : constant Natural :=
        Positive (Get_Logical_Line_Number (Obj.Span.Ptr));
      Col   : constant Natural := Positive (Get_Column_Number (Obj.Span.Ptr));

   begin
      Set_Field (Value, "file", File);
      Set_Field (Value, "line", Line);
      Set_Field (Value, "col", Col);
      Set_Field (Value, "message", To_JSON (Obj.Msg));

      if Obj.Msg.Secondary_Loc /= No_Location then
         declare
            Locations     : JSON_Array;
            Location      : constant JSON_Value := Create_Object;
            Phys_Location : constant JSON_Value := Create_Object;
            Region        : constant JSON_Value := Create_Object;
            File          : constant String :=
              File_Name (Obj.Msg.Secondary_Loc);
            Line          : constant Natural :=
              Positive (Get_Logical_Line_Number (Obj.Msg.Secondary_Loc));
            Col           : constant Natural :=
              Positive (Get_Column_Number (Obj.Msg.Secondary_Loc));
         begin
            Set_Field (Phys_Location, "uri", File);
            Set_Field (Region, "startLine", Line);
            Set_Field (Region, "startColumn", Col);
            Set_Field (Phys_Location, "region", Region);
            Set_Field (Location, "physicalLocation", Phys_Location);
            Set_Field (Location, "id", Integer'(0));
            Append (Locations, Location);
            Set_Field (Value, "relatedLocations", Locations);
         end;
      end if;

      if Obj.Suppr.Suppression_Kind in Warning | Check then
         declare
            Suppr_Reason : constant String :=
              (if Obj.Suppr.Suppression_Kind = Check
               then To_String (Obj.Suppr.Msg)
               else "");
         begin
            Set_Field (Value, "suppressed", Suppr_Reason);
            if Obj.Suppr.Suppression_Kind = Check then
               Set_Field
                 (Value,
                  "annot_kind",
                  To_Lower (Pretty_Annotation_Name (Obj.Suppr.Annot_Kind)));
               Set_Field
                 (Value, "justif_msg", To_String (Obj.Suppr.Justification));
            end if;
         end;
      end if;

      Set_Field (Value, "rule", Obj.Tag);
      Set_Field (Value, "severity", To_JSON (Obj.Severity));
      if Present (Obj.E) then
         Set_Field
           (Value, "entity", To_JSON (Entity_To_Subp_Assumption (Obj.E)));
      end if;
      Set_Field (Value, "check_tree", Obj.Check_Tree);
      Set_Field (Value, "unproved_status", To_JSON (Obj.Unproved_Stat));

      if Obj.VC_Loc /= No_Location then
         declare
            VC_File : constant String := File_Name (Obj.VC_Loc);
            VC_Line : constant Natural :=
              Positive (Get_Logical_Line_Number (Obj.VC_Loc));
            VC_Col  : constant Natural :=
              Positive (Get_Column_Number (Obj.VC_Loc));
         begin
            --  Note that vc_file already exists
            Set_Field (Value, "check_file", VC_File);
            Set_Field (Value, "check_line", VC_Line);
            Set_Field (Value, "check_col", VC_Col);
         end;
      end if;

      if Obj.Tracefile /= "" then
         Set_Field (Value, "tracefile", Obj.Tracefile);
      end if;

      if not Obj.Cntexmp.Map.Is_Empty then
         Set_Field (Value, "cntexmp", To_JSON (Obj.Cntexmp.Map));
      end if;

      if not Obj.Cntexmp.Input_As_JSON.Input_As_JSON.Is_Empty then
         Set_Field
           (Value, "cntexmp_value", To_JSON (Obj.Cntexmp.Input_As_JSON));
      end if;

      if Obj.VC_File /= "" then
         Set_Field (Value, "vc_file", Obj.VC_File);
      end if;

      if Obj.Editor_Cmd /= "" then
         Set_Field (Value, "editor_cmd", Obj.Editor_Cmd);
      end if;

      if Msg_Id /= No_Message_Id then
         Set_Field (Value, "msg_id", Natural (Msg_Id));
      end if;

      Set_Field (Value, "how_proved", To_JSON (Obj.How_Proved));

      if not Obj.Stats.Is_Empty then
         Set_Field (Value, "stats", To_JSON (Obj.Stats));
      end if;

      Append (Msg_List, Value);
   end Add_Json_Msg;

   ---------------
   -- From_JSON --
   ---------------

   function From_JSON (J : JSON_Value) return Failed_Prover_Answer is
      Status : constant String := Get (J, "status");
   begin
      if Status = "unknown" then
         return (Kind => FPA_Unknown);
      elsif Status = "gave_up" then
         return (Kind => FPA_Gave_Up);
      elsif Status = "limit" then
         return
           (Kind    => FPA_Limit,
            Timeout => Get (J, "time"),
            Step    => Get (J, "steps"),
            Memory  => Get (J, "memory"));
      else
         raise Program_Error;
      end if;
   end From_JSON;

   -----------
   -- Print --
   -----------

   procedure Print
     (Msg           : Message;
      Kind          : Msg_Severity := Error_Kind;
      Continuations : Message_Lists.List := Message_Lists.Empty)
   is

      procedure Print_Msg (Msg : Message; Cont : Boolean);
      --  encapsulate the logic of actually printing a message. Cont is true if
      --  this is a continuation message.

      function First_Explain_Code return Explain_Code_Kind;
      --  Return the first explain code found in the message or continuations
      --  (in that order).

      ------------------------
      -- First_Explain_Code --
      ------------------------

      function First_Explain_Code return Explain_Code_Kind is
      begin
         if Msg.Explain_Code /= EC_None then
            return Msg.Explain_Code;
         end if;
         for Cont of Continuations loop
            if Cont.Explain_Code /= EC_None then
               return Cont.Explain_Code;
            end if;
         end loop;
         return EC_None;
      end First_Explain_Code;

      ---------------
      -- Print_Msg --
      ---------------

      procedure Print_Msg (Msg : Message; Cont : Boolean) is
         Prefix      : constant String :=
           (case Kind is
              when Error_Kind        => "",
              when Warning_Kind      => "?",
              when Info_Kind         => "info: ",
              when Low_Check_Kind    => "low: ",
              when Medium_Check_Kind => "medium: ",
              when High_Check_Kind   => "high: ");
         Cont_Prefix : constant String :=
           (case Kind is
              when Error_Kind | Info_Kind => "\",
              when Warning_Kind           => "\?",
              when Check_Kind             =>
                (if Gnat2Why_Args.Output_Mode in GPO_Pretty
                 then "\"
                 else "\" & Prefix));
         use Node_Lists;
         Expl_Code   : constant String :=
           (if Msg.Explain_Code = EC_None
            then ""
            else " '[" & To_String (Msg.Explain_Code) & "']");
         C           : Cursor := Msg.Names.First;
      begin
         Errout.Error_Msg_Sloc := Msg.Secondary_Loc;
         if Has_Element (C) then
            Errout.Error_Msg_Node_1 := Element (C);
            Next (C);
            if Has_Element (C) then
               Errout.Error_Msg_Node_2 := Element (C);
               Next (C);
               if Has_Element (C) then
                  Errout.Error_Msg_Node_3 := Element (C);
                  Next (C);
                  if Has_Element (C) then
                     Errout.Error_Msg_Node_4 := Element (C);
                     Next (C);
                  end if;
               --  ??? ideally would need to go up to 6

               end if;
            end if;
         end if;
         declare
            S          : constant String :=
              (if Cont then Cont_Prefix else Prefix)
              & Escape_For_Errout (To_String (Msg.Msg))
              & Expl_Code;
            First_Node : constant Node_Id :=
              (if Msg.Names.Is_Empty
               then Types.Empty
               else First_Element (Msg.Names));
         begin
            Locate_Message (S, First_Node);
         end;
      end Print_Msg;

      --  Beginning of processing for Generic_Print_Result

   begin
      Print_Msg (Msg, Cont => False);
      for Cont of Continuations loop
         Print_Msg (Cont, Cont => True);
      end loop;
      declare
         Code : constant Explain_Code_Kind := First_Explain_Code;
      begin
         if Code /= EC_None then
            Print_Msg
              (Create
                 ("launch ""gnatprove --explain="
                  & To_String (Code)
                  & """ for more information"),
               Cont => True);
         end if;
      end;
   end Print;

   ------------
   -- Create --
   ------------

   function Create
     (Msg           : String;
      Names         : Node_Lists.List := Node_Lists.Empty;
      Secondary_Loc : Source_Ptr := No_Location;
      Explain_Code  : Explain_Code_Kind := EC_None) return Message is
   begin
      return
        Message'
          (Names, Secondary_Loc, Explain_Code, To_Unbounded_String (Msg));
   end Create;

   function Create_N
     (Msg           : String;
      Names         : String_Lists.List := String_Lists.Empty;
      Secondary_Loc : Source_Ptr := No_Location;
      Explain_Code  : Explain_Code_Kind := EC_None) return Message
   is
      Buf          : Unbounded_String;
      Current_Name : String_Lists.Cursor := Names.First;
      use type String_Lists.Cursor;
   begin
      --  Given that message objects hold lists of nodes, we need to do the
      --  replacement ourselves.
      for C of Msg loop
         if C = ''' then
            Append (Buf, C);
            Append (Buf, C);
         elsif C = '&' then
            Append (Buf, Names (Current_Name));
            String_Lists.Next (Current_Name);
         else
            Append (Buf, C);
         end if;
      end loop;

      --  All names should be substituted
      pragma Assert (Current_Name = String_Lists.No_Element);

      return Message'(Node_Lists.Empty, Secondary_Loc, Explain_Code, Buf);
   end Create_N;

   function Create_N
     (Kind          : Misc_Warning_Kind;
      Extra_Message : String := "";
      Names         : String_Lists.List := String_Lists.Empty;
      Secondary_Loc : Source_Ptr := No_Location;
      Explain_Code  : Explain_Code_Kind := EC_None) return Message is
   begin
      return
        Create_N
          (Warning_Message (Kind)
           & Extra_Message
           & (if Warning_Doc_Switch
              then " [" & Kind_Name (Kind) & "]"
              else ""),
           Names,
           Secondary_Loc,
           Explain_Code);
   end Create_N;

   ---------------
   -- Error_Msg --
   ---------------

   procedure Error_Msg
     (Msg           : Message;
      Span          : Source_Span;
      Kind          : Msg_Severity := Error_Kind;
      Continuations : Message_Lists.List := Message_Lists.Empty;
      Error_Entry   : Boolean := True)
   is

      procedure Span_Locate (Msg : String; First_Node : Node_Id);
      --  Procedure that holds the call to the errout backend, to be used with
      --  the generic Print procedure. The Span is used to locate the error
      --  message. First_Node is ignored.

      -----------------
      -- Span_Locate --
      -----------------

      procedure Span_Locate (Msg : String; First_Node : Node_Id) is
         pragma Unreferenced (First_Node);
      begin
         --  ??? We force the message to appear even if not on the main unit.
         --  This is to not hide messages that come from generic instances,
         --  inherited contracts, or inlined subprograms.
         --  This should only be done for flow/proof messages, and currently
         --  the Error_Msg procedure is only called by the proof machinery.

         Errout.Error_Msg (Msg & "!!", Span);
      end Span_Locate;

      procedure Local_Print_Result is new Print (Span_Locate);

      Result : constant JSON_Result_Type :=
        (Severity => Kind,
         Tag      => To_Unbounded_String ("error"),
         Span     => Span,
         Msg      => Msg,
         others   => <>);

      --  Beginning of processing for Error_Msg

   begin
      if Error_Entry then
         Add_Json_Msg (Warnings_Errors, Result);
      end if;
      Local_Print_Result (Msg, Kind, Continuations => Continuations);
   end Error_Msg;

   -----------------
   -- Error_Msg_N --
   -----------------

   procedure Error_Msg_N
     (Msg           : Message;
      N             : Node_Id;
      Kind          : Msg_Severity := Error_Kind;
      First         : Boolean := False;
      Continuations : Message_Lists.List := Message_Lists.Empty;
      Error_Entry   : Boolean := True;
      Tag           : String := "unknown-error")
   is

      procedure Node_Locate (Msg : String; First_Node : Node_Id);
      --  Procedure that holds the call to the errout backend, to be used with
      --  the generic Print procedure. The node N is used to locate the
      --  message, but Error_Msg_FE is called if First is set to True.

      -----------------
      -- Node_Locate --
      -----------------

      procedure Node_Locate (Msg : String; First_Node : Node_Id) is
      begin
         if First then
            Errout.Error_Msg_FE (Msg, N, First_Node);
         else
            Errout.Error_Msg_NE (Msg, N, First_Node);
         end if;
      end Node_Locate;

      procedure Local_Print_Result is new Print (Node_Locate);

      My_Msg   : constant Message := Add_Default_Name (Msg, N);
      My_Conts : Message_Lists.List;
      Result   : JSON_Result_Type :=
        (Severity => Kind,
         Tag      => To_Unbounded_String (Tag),
         Span     => To_Span (Sloc (N)),
         Msg      => My_Msg,
         others   => <>);
   begin
      for Msg of Continuations loop
         My_Conts.Append (Add_Default_Name (Msg, N));
      end loop;
      Result.Continuations := My_Conts;
      if Error_Entry then
         Add_Json_Msg (Warnings_Errors, Result);
      end if;
      Local_Print_Result (My_Msg, Kind, Continuations => My_Conts);
   end Error_Msg_N;

   procedure Error_Msg_N
     (Msg           : String;
      N             : Node_Id;
      Kind          : Msg_Severity := Error_Kind;
      Names         : Node_Lists.List := Node_Lists.Empty;
      Secondary_Loc : Source_Ptr := No_Location;
      Explain_Code  : Explain_Code_Kind := EC_None;
      First         : Boolean := False;
      Continuations : String_Lists.List := String_Lists.Empty)
   is
      Conts : Message_Lists.List := Message_Lists.Empty;
   begin
      for S of Continuations loop
         Conts.Append (Create (S));
      end loop;
      Error_Msg_N
        (Create (Msg, Names, Secondary_Loc, Explain_Code),
         N,
         Kind,
         First         => First,
         Continuations => Conts);
   end Error_Msg_N;

   procedure Error_Msg_N
     (Kind          : Error_Message_Kind;
      N             : Node_Id;
      Msg           : String := "";
      Names         : Node_Lists.List := Node_Lists.Empty;
      Secondary_Loc : Source_Ptr := No_Location;
      Explain_Code  : Explain_Code_Kind := EC_None;
      First         : Boolean := False;
      Continuations : String_Lists.List := String_Lists.Empty)
   is
      Actual_Msg : constant String :=
        (if Msg /= "" then Msg else Error_Message (Kind));
   begin
      Error_Msg_N
        (Actual_Msg,
         N,
         Error_Kind,
         Names,
         Secondary_Loc,
         Explain_Code,
         First         => First,
         Continuations => Continuations);
   end Error_Msg_N;

   ------------
   -- Escape --
   ------------

   function Escape (S : String) return String is
      R : Unbounded_String := Null_Unbounded_String;
      J : Integer := S'First;
      C : Character;
   begin
      while J <= S'Last loop
         C := S (J);
         if C in '&' | '#' then
            Append (R, ''');
         end if;

         J := J + 1;
         Append (R, C);
      end loop;

      return To_String (R);
   end Escape;

   -----------------------
   -- Escape_For_Errout --
   -----------------------

   function Escape_For_Errout (S : String) return String is
      R : Unbounded_String := Null_Unbounded_String;
      J : Integer := S'First;
      C : Character;
   begin
      while J <= S'Last loop
         C := S (J);
         if C = ''' and then J < S'Last and then S (J + 1) in '&' | '#' then
            Append (R, C);
            Append (R, S (J + 1));
            J := J + 2;
         elsif C
               in '%'
                | '$'
                | '{'
                | '*'
                | '}'
                | '@'
                | '^'
                | '>'
                | '!'
                | '?'
                | '<'
                | '`'
                | '''
                | '\'
                | '|'
                | '['
                | ']'
           or else Is_Upper (C)
         then
            Append (R, ''');
            J := J + 1;
            Append (R, C);
         else
            J := J + 1;
            Append (R, C);
         end if;

      end loop;

      return To_String (R);
   end Escape_For_Errout;

   ---------------------
   -- Next_Message_Id --
   ---------------------

   function Next_Message_Id return Message_Id is
      Result : constant Message_Id := Message_Id_Counter;
   begin
      Message_Id_Counter := @ + 1;
      return Result;
   end Next_Message_Id;

   ------------------
   -- Node_To_Name --
   ------------------

   function Node_To_Name (N : Node_Id) return String is
   begin
      case Nkind (N) is
         when N_Pragma =>
            return Raw_Source_Name (Pragma_Identifier (N));

         when others   =>
            return Raw_Source_Name (N);
      end case;
   end Node_To_Name;

   ----------------
   -- Tag_Suffix --
   ----------------

   function Tag_Suffix (Kind : Misc_Warning_Kind) return String is
   begin
      if Warning_Doc_Switch then
         return " [" & Kind_Name (Kind) & "]";
      else
         return "";
      end if;
   end Tag_Suffix;

   -------------
   -- To_JSON --
   -------------

   function To_JSON (Kind : Msg_Severity) return GNATCOLL.JSON.JSON_Value is
      S : constant String :=
        (case Kind is
           when Error_Kind        => "error",
           when Warning_Kind      => "warning",
           when Info_Kind         => "info",
           when High_Check_Kind   => "high",
           when Medium_Check_Kind => "medium",
           when Low_Check_Kind    => "low");
   begin
      return GNATCOLL.JSON.Create (S);
   end To_JSON;

   function To_JSON (M : Message) return JSON_Value is
      Result               : constant JSON_Value := Create_Object;
      Contains_Placeholder : Boolean;
      Msg_Text             : constant String :=
        To_SARIF_Msg_Text (M.Msg, Contains_Placeholder);
   begin
      Set_Field (Result, "text", Msg_Text);
      if not M.Names.Is_Empty and then Contains_Placeholder then
         declare
            Args : JSON_Array;
         begin
            for Node of M.Names loop
               Append (Args, Create (Node_To_Name (Node)));
            end loop;
            Set_Field (Result, "arguments", Args);
         end;
      end if;
      return Result;
   end To_JSON;

   -------------
   -- To_JSON --
   -------------

   function To_JSON (FPA : Failed_Prover_Answer) return JSON_Value is
      Result : constant JSON_Value := Create_Object;
   begin
      case FPA.Kind is
         when FPA_Unknown =>
            Set_Field (Result, "status", "unknown");

         when FPA_Gave_Up =>
            Set_Field (Result, "status", "gave_up");

         when FPA_Limit   =>
            Set_Field (Result, "status", "limit");
            Set_Field (Result, "time", FPA.Timeout);
            Set_Field (Result, "steps", FPA.Step);
            Set_Field (Result, "memory", FPA.Memory);
      end case;
      return Result;
   end To_JSON;

   -----------------------
   -- To_SARIF_Msg_Text --
   -----------------------

   function To_SARIF_Msg_Text
     (S : Unbounded_String; Contains_Placeholder : out Boolean) return String
   is
      Result  : Unbounded_String;
      Counter : Integer := 0;
      Index   : Integer := 1;
      Len     : constant Integer := Length (S);
   begin
      Contains_Placeholder := False;
      while Index in 1 .. Len loop
         case Element (S, Index) is
            when '''    =>
               if Index < Len and then Element (S, Index + 1) in '&' | '#' then
                  Append (Result, Element (S, Index + 1));
                  Index := Index + 1;
               else
                  Append (Result, ''');
               end if;

            when '&'    =>
               declare
                  Img : constant String := Counter'Img;
               begin
                  Append (Result, '{');
                  Append (Result, Img (Img'First + 1 .. Img'Last));
                  Append (Result, '}');
               end;
               Counter := Counter + 1;
               Contains_Placeholder := True;

            when '#'    =>
               Append (Result, "[here](0)");

            when others =>
               Append (Result, Element (S, Index));
         end case;
         Index := Index + 1;
      end loop;
      return To_String (Result);
   end To_SARIF_Msg_Text;

   -----------------
   -- To_User_Msg --
   -----------------

   function To_User_Msg (FPA : Failed_Prover_Answer) return String is
   begin
      case FPA.Kind is
         when FPA_Unknown =>
            return "";

         when FPA_Gave_Up =>
            return "provers gave up before completing the proof";

         when FPA_Limit   =>
            declare
               Limits_Text : Unbounded_String := Null_Unbounded_String;
            begin
               if FPA.Timeout then
                  Append (Limits_Text, "time");
               end if;
               if FPA.Step then
                  if Length (Limits_Text) > 0 then
                     if FPA.Memory then
                        Append (Limits_Text, ", ");
                     else
                        Append (Limits_Text, " and ");
                     end if;
                  end if;
                  Append (Limits_Text, "step");
               end if;
               if FPA.Memory then
                  if Length (Limits_Text) > 0 then
                     Append (Limits_Text, " and ");
                  end if;
                  Append (Limits_Text, "memory");
               end if;
               if Limits_Text = Null_Unbounded_String then
                  --  Should not happen
                  raise Program_Error;
               end if;
               return
                 "provers reached "
                 & To_String (Limits_Text)
                 & " limit before completing the proof";
            end;
      end case;
   end To_User_Msg;

   ---------------------------
   -- Warning_Is_Suppressed --
   ---------------------------

   function Warning_Is_Suppressed
     (N   : Node_Id;
      Msg : String;
      F1  : Flow_Id := Null_Flow_Id;
      F2  : Flow_Id := Null_Flow_Id;
      F3  : Flow_Id := Null_Flow_Id) return String_Id
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
         is ((Nkind (N) in N_Has_Entity
              and then Present (Entity (N))
              and then Has_Warnings_Off (Entity (N)))
             or else (Nkind (N) in N_Entity and then Has_Warnings_Off (N)));
         --  Returns True if N is an entity and Has_Warnings_Off (N)

         function Is_Entity_And_Has_Warnings_Off (F : Flow_Id) return Boolean
         is (F.Kind in Direct_Mapping | Record_Field
             and then
               Is_Entity_And_Has_Warnings_Off (Get_Direct_Mapping_Id (F)));

      begin
         --  ??? if Fn is not present, then there is no point to check F(n+1)
         return
           Is_Entity_And_Has_Warnings_Off (N)
           or else Is_Entity_And_Has_Warnings_Off (F1)
           or else Is_Entity_And_Has_Warnings_Off (F2)
           or else Is_Entity_And_Has_Warnings_Off (F3);
      end Warning_Disabled_For_Entity;

      Suppr_Reason : String_Id := Erroutc.Warnings_Suppressed (Sloc (N));

      --  Start of processing for Warning_Is_Suppressed

   begin
      if Suppr_Reason = No_String then
         Suppr_Reason :=
           Erroutc.Warning_Specifically_Suppressed
             (Loc => Sloc (N), Msg => Msg'Unrestricted_Access);

         if Suppr_Reason = No_String and then Warning_Disabled_For_Entity then
            Suppr_Reason := Null_String_Id;
         end if;
      end if;
      return Suppr_Reason;
   end Warning_Is_Suppressed;

   -------------------
   -- Warning_Msg_N --
   -------------------

   procedure Warning_Msg_N
     (Kind          : Misc_Warning_Kind;
      N             : Node_Id;
      Extra_Message : String := "";
      Names         : Node_Lists.List := Node_Lists.Empty;
      Secondary_Loc : Source_Ptr := No_Location;
      Explain_Code  : Explain_Code_Kind := EC_None;
      First         : Boolean := False;
      Continuations : Message_Lists.List := Message_Lists.Empty) is
   begin
      Warning_Msg_N
        (Kind,
         N,
         Create
           (Warning_Message (Kind) & Extra_Message & Tag_Suffix (Kind),
            Names,
            Secondary_Loc,
            Explain_Code),
         First,
         Continuations);
   end Warning_Msg_N;

   procedure Warning_Msg_N
     (Kind          : Misc_Warning_Kind;
      N             : Node_Id;
      Msg           : Message;
      First         : Boolean := False;
      Continuations : Message_Lists.List := Message_Lists.Empty)
   is
      Suppressed : constant Boolean :=
        Warning_Status (Kind) not in WS_Enabled | WS_Error;
      Severity   : constant Msg_Severity :=
        (if Warning_Status (Kind) = WS_Error
         then Error_Kind
         else Warning_Kind);
      My_Msg     : constant Message := Add_Default_Name (Msg, N);
      My_Conts   : Message_Lists.List;
   begin
      for Msg of Continuations loop
         My_Conts.Append (Add_Default_Name (Msg, N));
      end loop;
      if not Suppressed then
         Error_Msg_N (Msg, N, Severity, First, My_Conts, False);
      end if;
      declare
         --  The message can be suppressed via the warning tags, or via pragma
         --  Warnings (Off), check for the second way here.
         Was_Suppressed : constant Boolean :=
           Suppressed
           or else
             Warning_Is_Suppressed (N, To_String (My_Msg.Msg)) /= No_String;
         Result         : constant JSON_Result_Type :=
           JSON_Result_Type'
             (Msg           => My_Msg,
              Severity      => Severity,
              Tag           => To_Unbounded_String (Kind_Name (Kind)),
              Span          => To_Span (Sloc (N)),
              Suppr         =>
                (if Was_Suppressed
                 then Suppressed_Warning
                 else No_Suppressed_Message),
              Continuations => My_Conts,
              others        => <>);
      begin
         Add_Json_Msg (Warnings_Errors, Result);
      end;
   end Warning_Msg_N;

   function "&" (M : Message; S : String) return Message is
   begin
      return
        Message'
          (Names         => M.Names,
           Secondary_Loc => M.Secondary_Loc,
           Explain_Code  => M.Explain_Code,
           Msg           => M.Msg & S);
   end "&";

end Errout_Wrapper;
