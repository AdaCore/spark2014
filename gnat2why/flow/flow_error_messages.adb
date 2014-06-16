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
with Ada.Directories;
with Ada.Strings.Unbounded.Hash;
with Ada.Text_IO;                use Ada.Text_IO;

with GNATCOLL.JSON;

with Atree;                      use Atree;
with Einfo;                      use Einfo;
with Errout;                     use Errout;
with Erroutc;                    use Erroutc;
with Namet;                      use Namet;
with Opt;                        use Opt;
with Sem_Util;                   use Sem_Util;
with Sinfo;                      use Sinfo;
with Sinput;                     use Sinput;
with Stringt;                    use Stringt;
with String_Utils;               use String_Utils;
with VC_Kinds;

with Gnat2Why.Nodes;             use Gnat2Why.Nodes;
with Gnat2Why_Args;              use Gnat2Why_Args;

package body Flow_Error_Messages is

   type Msg_Kind is (Error_Kind, Warning_Kind, Info_Kind);
   --  describes the three kinds of messages issued by gnat2why

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

   procedure  Create_JSON_File
     (GNAT_Root : Node_Id;
      List      : GNATCOLL.JSON.JSON_Array;
      Suffix    : String);
   --  Write the JSON list in argument to the file "unit.suffix"

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
     (S : Unbounded_String;
      F : Flow_Id) return Unbounded_String;
   --  Find the first '&' or '#' and substitute with the given flow
   --  id, with or without enclosing quotes respectively.

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
         M := Substitute (M, F1);
      end if;
      if Present (F2) then
         M := Substitute (M, F2);
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

   ---------------------------
   -- Create_Flow_Msgs_File --
   ---------------------------

   procedure Create_Flow_Msgs_File (GNAT_Root : Node_Id) is
   begin
      Create_JSON_File (GNAT_Root, Flow_Msgs, VC_Kinds.Flow_Suffix);
   end Create_Flow_Msgs_File;

   ----------------------
   -- Create_JSON_File --
   ----------------------

   procedure  Create_JSON_File
     (GNAT_Root : Node_Id;
      List      : GNATCOLL.JSON.JSON_Array;
      Suffix    : String)
   is
      FD : Ada.Text_IO.File_Type;
      File_Name : constant String :=
        Ada.Directories.Compose
          (Name      => Spec_File_Name_Without_Suffix
             (Enclosing_Comp_Unit_Node (GNAT_Root)),
           Extension => Suffix);
      Full : constant GNATCOLL.JSON.JSON_Value :=
        GNATCOLL.JSON.Create (List);
   begin
      Ada.Text_IO.Create (FD, Ada.Text_IO.Out_File, File_Name);
      Ada.Text_IO.Put (FD, GNATCOLL.JSON.Write (Full, Compact => False));
      Ada.Text_IO.Close (FD);
   end Create_JSON_File;

   ----------------------------
   -- Create_Proof_Msgs_File --
   ----------------------------

   procedure Create_Proof_Msgs_File (GNAT_Root : Node_Id) is
   begin
      Create_JSON_File (GNAT_Root, Proof_Msgs, VC_Kinds.Proof_Suffix);
   end Create_Proof_Msgs_File;

   --------------------
   -- Error_Msg_Flow --
   --------------------

   procedure Error_Msg_Flow
     (FA        : Flow_Analysis_Graphs;
      Msg       : String;
      N         : Node_Id;
      F1        : Flow_Id               := Null_Flow_Id;
      F2        : Flow_Id               := Null_Flow_Id;
      Tag       : String                := "";
      SRM_Ref   : String                := "";
      Tracefile : String                := "";
      Warning   : Boolean               := False;
      Vertex    : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex)
   is
      E   : Entity_Id;
      Img : constant String := Natural'Image
        (FA.CFG.Vertex_To_Natural (Vertex));
      Tmp : constant String := (if Gnat2Why_Args.Flow_Advanced_Debug and then
                                  Vertex /= Flow_Graphs.Null_Vertex
                                then Msg & " <" & Img (2 .. Img'Last) & ">"
                                else Msg);
      Msg2 : constant String :=
        (if SRM_Ref'Length > 0 then Tmp & " (SPARK RM " & SRM_Ref & ")"
         else Tmp);
      Kind : constant Msg_Kind :=
        (if Warning then Warning_Kind else Error_Kind);
      Msg3 : constant String := Compute_Message (Msg2, N, F1, F2);
      Suppr : constant String_Id :=
        Warning_Is_Suppressed (N, Msg3, F1, F2);
      Slc   : constant Source_Ptr := Compute_Sloc (N);
      Msg_Id : Message_Id := No_Message_Id;
      Unb_Msg : constant Unbounded_String :=
        To_Unbounded_String (Msg3) &
        To_Unbounded_String (Source_Ptr'Image (Slc)) &
        To_Unbounded_String (Msg_Kind_To_String (Kind));
   begin
      --  If the message that we are about to emit has already been
      --  emitted in the past then we do nothing.

      if not Flow_Msgs_Set.Contains (Unb_Msg) then

         Flow_Msgs_Set.Insert (Unb_Msg);

         case FA.Kind is
            when E_Subprogram_Body | E_Package =>
               E := FA.Analyzed_Entity;
            when E_Package_Body =>
               E := Spec_Entity (FA.Analyzed_Entity);
         end case;

         --  print the message except when it's a suppressed warning

         if Kind = Error_Kind or else
           (Kind = Warning_Kind and then
              Suppr = No_String)
         then
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

         --  set the error flag if we have an error or an unsuppressed warning
         --  with warnings-as-errors

         if Kind = Error_Kind or else
           (Kind = Warning_Kind and then
              Opt.Warning_Mode = Treat_As_Error and then
              Suppr = No_String)
         then
            Found_Flow_Error := True;
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
      Tag         : String;
      Tracefile   : String;
      VC_File     : String;
      Editor_Cmd  : String;
      E           : Entity_Id;
      Place_First : Boolean) is
      Kind   : constant Msg_Kind :=
        (if Is_Proved then Info_Kind else Warning_Kind);
      Msg2   : constant String :=
        Compute_Message (Msg, N);
      Suppr  : constant String_Id := Warning_Is_Suppressed (N, Msg2);
      Slc    : constant Source_Ptr := Compute_Sloc (N, Place_First);
      Msg_Id : Message_Id := No_Message_Id;
   begin
      case Kind is
         when Warning_Kind =>
            if Suppr = No_String then
               Msg_Id := Print_Regular_Msg (Msg2, Slc, Kind);
            end if;
         when Info_Kind =>
            if Report_Mode /= GPR_Fail then
               Msg_Id := Print_Regular_Msg (Msg2, Slc, Kind);
            end if;
         when Error_Kind =>
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

      use GNATCOLL.JSON;

      Value     : constant JSON_Value := Create_Object;
      File       : constant String := File_Name (Slc);
      Line       : constant Integer :=
        Integer (Get_Logical_Line_Number (Slc));
      Col        : constant Integer := Integer (Get_Column_Number (Slc));
   begin
      Set_Field (Value, "file", File);
      Set_Field (Value, "line", Line);
      Set_Field (Value, "col", Col);

      if Kind = Warning_Kind and then Suppr /= No_String then
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

      Set_Field (Value, "rule",
                 (if Suppr /= No_String then "pragma_warning" else Tag));

      Set_Field (Value, "severity", Msg_Kind_To_String (Kind));

      --  Append entity information

      declare
         Ent_Value : constant JSON_Value := Create_Object;
         Loc       : constant Source_Ptr := Translate_Location (Sloc (E));
      begin
         Set_Field (Ent_Value, "file", File_Name (Loc));
         Set_Field (Ent_Value, "line",
                    Integer (Get_Physical_Line_Number (Loc)));
         Set_Field (Ent_Value, "name", Subprogram_Full_Source_Name (E));
         Set_Field (Value, "entity", Ent_Value);
      end;

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
      Id : constant Message_Id := Message_Id_Counter;
      Actual_Msg : constant String :=
        (if Kind = Info_Kind then "info: " else "") &
        Escape (Msg) & "!!" &
      (if Kind /= Error_Kind then "?" else "") &
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
     (S : Unbounded_String;
      F : Flow_Id) return Unbounded_String
   is
      R      : Unbounded_String := Null_Unbounded_String;
      Do_Sub : Boolean          := True;
      Quote  : Boolean;
   begin
      for Index in Positive range 1 .. Length (S) loop
         if Do_Sub and then Element (S, Index) in '&' | '#' then
            Quote := Element (S, Index) = '&';

            if Quote then
               Append (R, """");
            end if;

            case F.Kind is
               when Null_Value =>
                  raise Program_Error;

               when Synthetic_Null_Export =>
                  Append (R, "null");

               when Direct_Mapping | Record_Field =>
                  Append (R, Flow_Id_To_String (F));

                  case F.Bound.Kind is
                     when No_Bound =>
                        null;

                     when Some_Bound =>
                        Append (R, "'Some_Bound");
                        --  raise Program_Error;
                  end case;

               when Magic_String =>
                  --  ??? we may want to use __gnat_decode() here instead
                  if F.Name.all = "__HEAP" then
                     Append (R, "the heap");
                  else
                     declare
                        Index : Positive := 1;
                     begin
                        --  Replace __ with . in the magic string.
                        while Index <= F.Name.all'Length loop
                           case F.Name.all (Index) is
                              when '_' =>
                                 if Index < F.Name.all'Length and then
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

         function Is_Entity_And_Has_Warnings_Off (N : Node_Or_Entity_Id)
                                                  return Boolean
         is ((Is_Entity_Name (N) and then Has_Warnings_Off (Entity (N)))
             or else (Nkind (N) in N_Entity and then Has_Warnings_Off (N)));
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
