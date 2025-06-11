with Ada.Characters.Handling; use Ada.Characters.Handling;
with Assumption_Types;        use Assumption_Types;
with Atree;                   use Atree;
with Gnat2Why_Args;
with Gnat2Why_Opts;           use Gnat2Why_Opts;
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
      First_Node    : Node_Id := Empty;
      Continuations : Message_Lists.List := Message_Lists.Empty);
   --  Prepare the call to the Errout backend, e.g. Errout.Error_Msg_N.
   --  The actual call shall be made by the generic argument procedure.
   --  First_Node - this node, if present, is used to set the map of names, and
   --               is passed to Locate_Message.

   function Create_N
     (Msg           : String;
      Names         : String_Lists.List := String_Lists.Empty;
      Secondary_Loc : Source_Ptr := No_Location;
      Explain_Code  : Explain_Code_Kind := EC_None) return Message;
   --  Same as Create, but the names can be provided as a list of Strings.

   function To_JSON (M : Message) return JSON_Value;
   --  Transform message object into JSON (SARIF) message object

   function Node_To_Name (N : Node_Id) return String;
   --  Convert the node to a String. This is mostly a wrapper around
   --  Source_Name.

  ------------------
   -- Add_Json_Msg --
   ------------------

   procedure Add_Json_Msg
     (Msg_List : in out GNATCOLL.JSON.JSON_Array;
      Obj      : JSON_Result_Type;
      Msg_Id   : Message_Id)
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
                 (Value, "annot_kind", To_String (Obj.Suppr.Annot_Kind));
               Set_Field
                 (Value, "justif_msg", To_String (Obj.Suppr.Justification));
            end if;
         end;
      end if;

      Set_Field (Value, "rule", Obj.Tag);
      Set_Field (Value, "severity", To_JSON (Obj.Severity));
      Set_Field (Value, "entity", To_JSON (Entity_To_Subp_Assumption (Obj.E)));
      Set_Field (Value, "check_tree", Obj.Check_Tree);

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

   --------------------------
   -- Generic_Print_Result --
   --------------------------

   procedure Print
     (Msg           : Message;
      Kind          : Msg_Severity := Error_Kind;
      First_Node    : Node_Id := Empty;
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
              when Error_Kind => "",
              when Warning_Kind => "?",
              when Info_Kind => "info: ",
              when Low_Check_Kind => "low: ",
              when Medium_Check_Kind => "medium: ",
              when High_Check_Kind => "high: ");
         Cont_Prefix : constant String :=
           (case Kind is
              when Error_Kind | Info_Kind => "\",
              when Warning_Kind => "\?",
              when Check_Kind =>
                (if Gnat2Why_Args.Output_Mode in GPO_Pretty
                 then "\"
                 else "\" & Prefix));
         use Node_Lists;
         Expl_Code   : constant String :=
           (if Msg.Explain_Code = EC_None
            then ""
            else " '[" & To_String (Msg.Explain_Code) & "']");
         Names       : constant Node_Lists.List :=
           (if Present (First_Node) and then Msg.Names.Is_Empty
            then Node_Lists.List'([First_Node])
            else Node_Lists.List'(Msg.Names));
         C           : Cursor := Names.First;
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
              (if Names.Is_Empty then Types.Empty else First_Element (Names));
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
      Continuations : Message_Lists.List := Message_Lists.Empty)
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

      --  Beginning of processing for Error_Msg

   begin
      Local_Print_Result
        (Msg, Kind, First_Node => Empty, Continuations => Continuations);
   end Error_Msg;

   -----------------
   -- Error_Msg_N --
   -----------------

   procedure Error_Msg_N
     (Msg           : Message;
      N             : Node_Id;
      Kind          : Msg_Severity := Error_Kind;
      First         : Boolean := False;
      Continuations : Message_Lists.List := Message_Lists.Empty)
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

   begin
      Local_Print_Result
        (Msg, Kind, First_Node => N, Continuations => Continuations);
   end Error_Msg_N;

   -----------------
   -- Error_Msg_N --
   -----------------

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
            return Source_Name (Pragma_Identifier (N));

         when others =>
            return Source_Name (N);
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
           when Error_Kind => "error",
           when Warning_Kind => "warning",
           when Info_Kind => "info",
           when High_Check_Kind => "high",
           when Medium_Check_Kind => "medium",
           when Low_Check_Kind => "low");
   begin
      return GNATCOLL.JSON.Create (S);
   end To_JSON;

   function To_JSON (M : Message) return JSON_Value is
      Result : constant JSON_Value := Create_Object;
   begin
      Set_Field (Result, "text", To_String (M.Msg));
      if not M.Names.Is_Empty then
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
      Continuations : Message_Lists.List := Message_Lists.Empty) is
   begin
      if Warning_Status (Kind) in WS_Enabled | WS_Error then
         Error_Msg_N
           (Msg,
            N,
            (if Warning_Status (Kind) = WS_Enabled
             then Warning_Kind
             else Error_Kind),
            First,
            Continuations);
      end if;
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
