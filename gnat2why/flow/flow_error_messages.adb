------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                  F L O W _ E R R O R _ M E S S A G E S                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2013-2016, Altran UK Limited              --
--                  Copyright (C) 2013-2016, AdaCore                        --
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

with Ada.Containers.Indefinite_Ordered_Maps;
with Ada.Containers.Doubly_Linked_Lists;
with Ada.Strings;                use Ada.Strings;
with Ada.Strings.Fixed;          use Ada.Strings.Fixed;
with Ada.Strings.Unbounded;      use Ada.Strings.Unbounded;
with Assumption_Types;           use Assumption_Types;
with Atree;                      use Atree;
with Common_Containers;          use Common_Containers;
with Csets;                      use Csets;
with Einfo;                      use Einfo;
with Errout;                     use Errout;
with Erroutc;                    use Erroutc;
with Flow_Utility;               use Flow_Utility;
with Gnat2Why.Annotate;          use Gnat2Why.Annotate;
with Gnat2Why.Assumptions;       use Gnat2Why.Assumptions;
with Gnat2Why_Args;              use Gnat2Why_Args;
with GNATCOLL.Utils;             use GNATCOLL.Utils;
with GNAT;                       use GNAT;
with GNAT.String_Split;
with Namet;                      use Namet;
with Sinfo;                      use Sinfo;
with Sinput;                     use Sinput;
with SPARK_Util;                 use SPARK_Util;
with Stringt;                    use Stringt;

package body Flow_Error_Messages is

   Flow_Msgs_Set : String_Sets.Set;
   --  Container with flow-related messages; used to prevent duplicate messages

   function Msg_Severity_To_String (Severity : Msg_Severity) return String;
   --  Transform the msg kind into a string, for the JSON output.

   type Message_Id is new Integer range -1 .. Integer'Last;
   --  type used to identify a message issued by gnat2why

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
      return Source_Ptr;
   --  function to compute a better sloc for reporting of results than the Ada
   --  Node. This takes into account generics.
   --  @param N the node for which we compute the sloc
   --  @param Place_First set this boolean to true to obtain placement at the
   --                     first sloc of the node, instead of the topmost node
   --  @return a sloc

   procedure Add_Json_Msg
     (Suppr       : String_Id;
      Tag         : String;
      Severity    : Msg_Severity;
      Slc         : Source_Ptr;
      Msg_List    : in out GNATCOLL.JSON.JSON_Array;
      E           : Entity_Id;
      Msg_Id      : Message_Id;
      Tracefile   : String := "";
      Cntexmp     : JSON_Value := GNATCOLL.JSON.Create_Object;
      VC_File     : String := "";
      How_Proved  : String := "";
      Stats       : JSON_Value := GNATCOLL.JSON.Create_Object;
      Editor_Cmd  : String := "");

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

   Flow_Msgs : GNATCOLL.JSON.JSON_Array;
   --  This will hold all of the emitted flow messages in JSON format.

   Proof_Msgs : GNATCOLL.JSON.JSON_Array;

   use type Ada.Containers.Count_Type;
   use type Flow_Graphs.Vertex_Id;
   use type Flow_Id_Sets.Set;

   function Escape (S : String) return String;
   --  Escape any special characters used in the error message (for
   --  example transforms "=>" into "='>" as > is a special insertion
   --  character. We also escape capital letters.

   function Substitute
     (S    : Unbounded_String;
      F    : Flow_Id;
      Flag : Source_Ptr)
      return Unbounded_String;
   --  Find the first '&' or '%' and substitute with the given flow id,
   --  with or without enclosing quotes respectively. Alternatively, '#'
   --  works like '&', but is followed by a line reference. Use '@' to
   --  substitute only with sloc of F.

   File_Counter : Natural := 0;
   Message_Id_Counter : Message_Id := 0;
   No_Message_Id : constant Message_Id := -1;

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

               Context :=
                 To_Unbounded_String (if Comes_From_Inlined_Body (Tmp)
                                      then ", in call inlined at "
                                      else ", in instantiation at ");

               Tmp := Instantiation_Location (Tmp);
               File := To_Unbounded_String (File_Name (Tmp));
               Line := Get_Physical_Line_Number (Tmp);
               Append (M, To_String (Context) &
                         To_String (File) & ":" & Image (Integer (Line), 1));
            end loop;
         end;
      end if;
      return To_String (M);
   end Compute_Message;

   function Compute_Sloc
     (N           : Node_Id;
      Place_First : Boolean := False) return Source_Ptr
   is
      Slc : Source_Ptr := (if Place_First
                           then First_Sloc (N)
                           else Sloc (N));
   begin
      if Instantiation_Location (Slc) /= No_Location then
         --  If we are dealing with an instantiation of a generic we change
         --  the message to point at the implementation of the generic and we
         --  mention where the generic is instantiated.
         Slc := Original_Location (Slc);
      end if;
      return Slc;
   end Compute_Sloc;

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
      Continuation : Boolean := False)
   is
      Msg2    : constant String :=
        (if SRM_Ref'Length > 0 then Msg & " (SPARK RM " & SRM_Ref & ")"
         else Msg);

      Msg3 : constant String     := Compute_Message (Msg2, N, F1, F2, F3);
      Slc  : constant Source_Ptr := Compute_Sloc (N);

      Msg_Str : constant String :=
        Msg3 &
        Source_Ptr'Image (Slc) &
        Integer'Image (Msg_Severity'Pos (Severity));

      Suppr  : String_Id  := No_String;
      Msg_Id : Message_Id := No_Message_Id;

      function Is_Specified_Line return Boolean;
      --  Returns True if command line argument "--limit-line" was not
      --  given, or if the message currently being processed is to
      --  be emitted on the line specified by the "--limit-line"
      --  argument.

      -----------------------
      -- Is_Specified_Line --
      -----------------------

      function Is_Specified_Line return Boolean is
         Loc  : constant Source_Ptr := Translate_Location (Sloc (N));
         File : constant String := File_Name (Loc);
         Line : constant Physical_Line_Number :=
           Get_Physical_Line_Number (Loc);
      begin
         return Gnat2Why_Args.Limit_Line = Null_Unbounded_String
           or else File & ":" & Image (Integer (Line), 1) =
                     To_String (Gnat2Why_Args.Limit_Line);
      end Is_Specified_Line;

      Dummy    : String_Sets.Cursor;
      Inserted : Boolean;

   --  Start of processing for Error_Msg_Flow

   begin
      --  If the message we are about to emit has already been emitted
      --  in the past then do nothing.

      Flow_Msgs_Set.Insert (New_Item => Msg_Str,
                            Position => Dummy,
                            Inserted => Inserted);

      if Inserted then
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
               --  Set the error flag if we have an error message. Note
               --  that warnings do not count as errors here, they should
               --  not prevent us going to proof. The errout mechanism
               --  already deals with the warnings-as-errors handling for
               --  the whole unit.
               Suppressed       := False;
               Found_Flow_Error := True;
         end case;

         --  Print the message except when it's suppressed.
         --  Additionally, if command line argument "--limit-line" was
         --  given, only issue the warning if it is to be emitted on
         --  the specified line (errors are emitted anyway).

         if not Suppressed and then Is_Specified_Line then
            Msg_Id := Print_Regular_Msg (Msg3, Slc, Severity, Continuation);
         end if;

         Add_Json_Msg
           (Suppr     => Suppr,
            Tag       => Flow_Tag_Kind'Image (Tag),
            Severity  => Severity,
            Slc       => Slc,
            Msg_List  => Flow_Msgs,
            E         => E,
            Tracefile => Tracefile,
            Msg_Id    => Msg_Id);
      else
         Suppressed := True;
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
      Tracefile    : String                := "";
      Vertex       : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex;
      Continuation : Boolean               := False)
   is
      Img     : constant String := Natural'Image
        (FA.CFG.Vertex_To_Natural (Vertex));
      Tmp     : constant String :=
        (if Gnat2Why_Args.Flow_Advanced_Debug
           and then Vertex /= Flow_Graphs.Null_Vertex
         then Msg & " <" & Img (2 .. Img'Last) & ">"
         else Msg);
      Suppressed : Boolean;

      E : constant Entity_Id :=
        (if FA.Kind = Kind_Package_Body
         then Spec_Entity (FA.Analyzed_Entity)
         else FA.Analyzed_Entity);

   begin
      Error_Msg_Flow (E            => E,
                      Msg          => Tmp,
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
      Tag         : VC_Kind;
      Tracefile   : String;
      Cntexmp     : JSON_Value := Create_Object;
      VC_File     : String;
      Editor_Cmd  : String;
      E           : Entity_Id;
      How_Proved  : String;
      Stats       : JSON_Value := Create_Object;
      Place_First : Boolean)
   is
      function JSON_Get_Opt (Val : JSON_Value; Field : String;
                             Opt_Result : JSON_Value) return JSON_Value is
        (if Has_Field (Val, Field) then Get (Val, Field)
         else Opt_Result);

      function Create_Pretty_Cntexmp (Cntexmp : JSON_Value;
                                      VC_Loc  : Source_Ptr) return JSON_Value;
      --  Create pretty printed counterexample.
      --  Note that deep copy of Cntexmp is made and thus the content of
      --  Cntexmp is not impacted by pretty printing.
      --  @param Cntexmp the counterexample that is pretty printed
      --  @param VC_Loc the location of the construct that triggers VC
      --  @return pretty printed counterexample.

      function Get_Cntexmp_One_Liner
        (Cntexmp : JSON_Value; VC_Loc : Source_Ptr) return String;
      --  Get the part of the counterexample corresponding to the location of
      --  the construct that triggers VC.

      function Get_Severity
        (N         : Node_Id;
         Is_Proved : Boolean;
         Tag       : VC_Kind) return Msg_Severity;
      --  @result Severity of the proof message

      ---------------------------
      -- Create_Pretty_Cntexmp --
      ---------------------------

      function Create_Pretty_Cntexmp (Cntexmp : JSON_Value;
                                      VC_Loc  : Source_Ptr) return JSON_Value
      is
         procedure Gen_JSON_Object is new
           Gen_Map_JSON_Object (Mapped => JSON_Value);

         procedure Create_Pretty_File (Pretty_Cntexmp : in out JSON_Value;
                                       File : String;
                                       File_Cntexmp : JSON_Value);
         --  Creates counterexample file with pretty printed model element
         --  names and adds the counterexample file into the Pretty_Cntexmp
         --  @param Pretty_Cntexmp pretty printed counterexample
         --  @param File the name of the field of Pretty_Cntexmp to that pretty
         --    printed counterexample file should be added.
         --    Note that if it is not Ada file, the file will not be added.
         --  @param File_Cntexmp counterexample file before pretty printing

         ------------------------
         -- Create_Pretty_File --
         ------------------------

         procedure Create_Pretty_File (Pretty_Cntexmp : in out JSON_Value;
                                       File : String;
                                       File_Cntexmp : JSON_Value)
         is
            procedure Create_Pretty_Line
              (Pretty_File_Cntexmp : in out JSON_Value;
               Line : String;
               Line_Cntexmp : JSON_Value);
            --  Pretty prints counterexample model elements at a single source
            --  code location (line).

            ------------------------
            -- Create_Pretty_Line --
            ------------------------

            procedure Create_Pretty_Line
              (Pretty_File_Cntexmp : in out JSON_Value;
               Line : String;
               Line_Cntexmp : JSON_Value)
            is
               type CNT_Element (<>);
               type CNT_Element_Ptr is access all CNT_Element;

               package CNT_Elements is
                 new Ada.Containers.Indefinite_Ordered_Maps
                   (Key_Type => String,
                    Element_Type => CNT_Element_Ptr
                   );

               type CNT_Element_Map_Ptr is access all
                 CNT_Elements.Map;

               package Vars_List is
                 new Ada.Containers.Doubly_Linked_Lists
                   (Element_Type => Unbounded_String);

               --  Represents variables at given source code location.
               type Variables_Info is record
                  Variables_Order : Vars_List.List;
                  --  Vector of variable names in the order in that variables
                  --  should be displayed

                  Variables_Map : aliased CNT_Elements.Map;
                  --  Map from variable names to information about these
                  --  variables. This includes values of variables,
                  --  informations about possible record fields and
                  --  informations about possible attributes.
               end record;

               use CNT_Elements;

               --  Represents information about the element of a counter
               --  example. An element can be either:
               --  - a variable/field/attribute of a record type, in which case
               --    Value = "@not_display",
               --    Fields contains the CNT_Element of some/all of its fields
               --    and Attributes may contain info on its attributes.
               --  - a "flat" variable/field/attribute, in which case
               --    Value is set to the counter example value
               --    Fields is empty
               --    and Attributes may contain info on its attributes.
               type CNT_Element
               is record
                  Entity : Entity_Id;
                  --  The corresponding element of SPARK AST

                  Attributes : CNT_Element_Map_Ptr;
                  Fields     : CNT_Element_Map_Ptr;
                  Value      : Unbounded_String;
               end record;

               function Print_CNT_Element_Debug (El : CNT_Element)
                                                 return String;
               --  Debug function, print a CNT_Element without any processing
               function Print_CNT_Element_Debug (El : CNT_Element)
                                                 return String
               is
                  R : Unbounded_String := "[ " & El.Value & " | ";
               begin
                  for F in El.Fields.Iterate loop
                     R := R & "<F- " & CNT_Elements.Key (F) &
                       " = " &
                       Print_CNT_Element_Debug (CNT_Elements.Element (F).all)
                     & " -F>";
                  end loop;

                  for F in El.Attributes.Iterate loop
                     R := R & "<A- " & CNT_Elements.Key (F) &
                       " = " &
                       Print_CNT_Element_Debug (CNT_Elements.Element (F).all)
                       & " -A>";
                  end loop;

                  return To_String (R & " ]");
               end Print_CNT_Element_Debug;

               Dont_Display : constant Unbounded_String :=
                 To_Unbounded_String ("@not_display");

               procedure Build_Variables_Info
                 (Line_Cntexmp_Arr : JSON_Array;
                  Variables : in out Variables_Info);
               --  Build a structure holding the informations associated to
               --  the counterexample at a single source code location.
               --  This structure associates to each variable mentioned in the
               --  counterexample a CNT_Element gathering the infos given in
               --  the counter example (fields if any, attributes and
               --  associated value(s)).
               --  @param Line_Cntexmp_Arr counterexample model elements at a
               --    single source code location (line)
               --  @param Variables stores information about values, fields
               --    and or attributes of variables at a single source code
               --    location.

               --------------------------
               -- Build_Variables_Info --
               --------------------------

               procedure Build_Variables_Info
                 (Line_Cntexmp_Arr : JSON_Array;
                  Variables : in out Variables_Info)
               is
                  function Insert_CNT_Element
                    (Name    : String;
                     Entity  : Entity_Id;
                     Map     : CNT_Element_Map_Ptr)
                     return CNT_Element_Ptr;
                  --  Insert a CNT_Element with given name and entity to
                  --  the given map.
                  --  If it has already been inserted, return the existing.
                  --  If not, create new entry, store it in the map,
                  --  and return it.

                  -------------------------
                  -- Insert_CNT_Element --
                  -------------------------

                  function Insert_CNT_Element
                    (Name    : String;
                     Entity  : Entity_Id;
                     Map     : CNT_Element_Map_Ptr)
                     return CNT_Element_Ptr
                  is
                     Var : CNT_Element_Ptr;
                  begin

                     if Contains (Map.all, Name)
                     then
                        Var := Element (Map.all, Name);
                     else
                        Var := new CNT_Element'
                          (Entity     => Entity,
                           Attributes => new CNT_Elements.Map,
                           Fields     => new CNT_Elements.Map,
                           Value      => Dont_Display);

                        Include (Container => Map.all,
                                 Key       => Name,
                                 New_Item  => Var);
                     end if;

                     return Var;

                  end Insert_CNT_Element;

               --  Start of processing for Build_Variables_Info

               begin
                  for Var_Index in Positive
                    range 1 .. Length (Line_Cntexmp_Arr)
                  loop
                     declare
                        Cntexmp_Element : constant JSON_Value :=
                          Get (Line_Cntexmp_Arr, Var_Index);
                        Name  : constant String :=
                          Get (Cntexmp_Element, "name");
                        Kind  : constant String :=
                          Get (Cntexmp_Element, "kind");
                        Value : constant String :=
                          Get (Cntexmp_Element, "value");
                        Name_Parts : String_Split.Slice_Set;
                        Current_Subfields_Map : CNT_Element_Map_Ptr :=
                          Variables.Variables_Map'Unchecked_Access;
                        Current_Attributes_Map : CNT_Element_Map_Ptr :=
                          new CNT_Elements.Map;
                     begin

                        --  There is either one model element with its name
                        --  corresponding to an error message. No variable map
                        --  is built in this case.

                        if Kind = "error_message" then
                           return;
                        end if;

                        --  If the value of a model element contains "@",
                        --  it is an abstract value that should not be
                        --  displayed.
                        --  To display such value, projection to SPARK value
                        --  must be defined.
                        --  These internal values can appear because there are
                        --  not yet defined projections. These are mainly the
                        --  values of types defined in share/spark/theories

                        if Index (Value, "@") /= 0 then
                           goto Next_Model_Element;
                        end if;

                        --  model elements are of the form:
                        --  Name ::= | Variable
                        --           | Variable "." Record_Fields
                        --           | Variable "'" Attributes
                        --  Record_Fields ::= | Record_Field "." Record_Fields
                        --                    | Record_Field "'" Attributes
                        --                    | Record_Field
                        --  Attributes ::= | Attribute "." Record_Fields
                        --                 | Attribute "'" Attributes
                        --                 | Attribute
                        --  Variable ::= ENTITY_ID
                        --  Record_Field ::= ENTITY_ID
                        --  Attribute ::= STRING
                        --
                        --  The ENTITY_ID in first Part corresponds to a
                        --  variable, others to record fields.

                        --  Split Name into sequence of Part

                        String_Split.Create (S => Name_Parts,
                                             From => Name,
                                             Separators => ".'",
                                             Mode => String_Split.Single);

                        --  For every Part, we create a CNT_Element.

                        for Var_Slice_Num in 1 .. String_Split.Slice_Count
                          (Name_Parts) loop
                           declare
                              function Is_Uninitialized
                                (Element_Decl : Entity_Id;
                                 Element_File : String;
                                 Element_Line : Logical_Line_Number)
                                 return Boolean;
                              --  Return True if the counterexample element
                              --  with given declaration at given position
                              --  is uninitialized.

                              ----------------------
                              -- Is_Uninitialized --
                              ----------------------

                              function Is_Uninitialized
                                (Element_Decl : Entity_Id;
                                 Element_File : String;
                                 Element_Line : Logical_Line_Number)
                                 return Boolean is
                              begin
                                 --  Counterexample element can be
                                 --  uninitialized only if its location is
                                 --  the same as location of its declaration
                                 --  (otherwise it has been assigned or it is
                                 --  a part of construct that triggers VC - and
                                 --  flow analysis would issue an error in this
                                 --  case).
                                 if File_Name
                                     (Sloc (Element_Decl)) = Element_File
                                     and then
                                   Get_Logical_Line_Number
                                      (Sloc (Element_Decl)) = Element_Line
                                 then
                                    case Nkind (Parent (Element_Decl)) is
                                    --  Uninitialized variable
                                    when N_Object_Declaration =>
                                       declare
                                          No_Init_Expr : constant Boolean :=
                                            No (Expression
                                                (Parent (Element_Decl)));
                                          No_Default_Init : constant Boolean :=
                                            Default_Initialization
                                              (Etype (Element_Decl)) =
                                                No_Default_Initialization;
                                       begin
                                          return No_Init_Expr
                                            and then No_Default_Init;
                                       end;

                                    --  Uninitialized function argument
                                    when N_Formal_Object_Declaration |
                                         N_Parameter_Specification   =>
                                       return
                                         Out_Present (Parent (Element_Decl))
                                         and then
                                         not
                                           In_Present (Parent (Element_Decl));

                                    when others =>
                                       return False;
                                    end case;

                                 end if;

                                 return False;
                              end Is_Uninitialized;

                              function Try_Get_Part_Entity (Part : String)
                                                            return Entity_Id;
                              --  Try to cast Part into an Entity_Id,
                              --  return empty id if it doesn't work.
                              function Try_Get_Part_Entity (Part : String)
                                                            return Entity_Id is
                              begin
                                 return Entity_Id'Value (Part);
                              exception
                                 when Constraint_Error =>
                                    return Empty;
                              end Try_Get_Part_Entity;

                              use GNAT.String_Split;

                              Part : constant String :=
                                Slice (Name_Parts, Var_Slice_Num);

                              Part_Entity : constant Entity_Id :=
                                Try_Get_Part_Entity (Part);
                              --  Note that if Var_Slice_Num = 1, Part_Entity
                              --  is Entity_Id of either declaration of
                              --  argument of a function or declaration of a
                              --  variable (corresponding to the counterexample
                              --  element being processed)
                              --  If Var_Slice_Num > 1, Part_Entity is
                              --  Entity_Id of declaration of record field or
                              --  discriminant.

                              Is_Attribute : Boolean :=
                                No (Part_Entity);
                              --  If Part does not cast into an entity_id it is
                              --  treated as an attribute.

                              Part_Name : Unbounded_String :=
                                To_Unbounded_String
                                  (if Is_Attribute
                                   then Part
                                   else Source_Name (Part_Entity));
                              Current_CNT_Element : CNT_Element_Ptr;

                           begin
                              if Var_Slice_Num = 1 then

                                 --  Process the first Entity_Id, which
                                 --  corresponds to a variable.

                                 --  Do not display uninitialized
                                 --  counterexample elements (elements
                                 --  corresponding to uninitialized variables
                                 --  or function arguments)
                                 if Is_Uninitialized
                                   (Part_Entity,
                                    File,
                                    Logical_Line_Number'Value (Line))
                                 then
                                    goto Next_Model_Element;
                                 end if;

                                 --  Store variable name to Variable_List
                                 if not Vars_List.Contains
                                   (Variables.Variables_Order,
                                    Part_Name)
                                 then
                                    Vars_List.Append
                                      (Variables.Variables_Order,
                                       Part_Name);
                                 end if;

                                 --  Possibly Append attributes 'Old or
                                 --  'Result after its name
                                 if (Kind = "old"
                                       and then
                                       Nkind (Parent (Part_Entity)) in
                                          N_Formal_Object_Declaration |
                                          N_Parameter_Specification
                                       and then
                                       Out_Present (Parent (Part_Entity)))
                                   or else Kind = "result"
                                 then
                                    Current_CNT_Element := Insert_CNT_Element
                                      (Name   => To_String (Part_Name),
                                       Entity => Part_Entity,
                                       Map    => Current_Subfields_Map);

                                    Current_Subfields_Map :=
                                      Current_CNT_Element.Fields;
                                    Current_Attributes_Map :=
                                      Current_CNT_Element.Attributes;

                                    Part_Name := To_Unbounded_String
                                      (if Kind = "old"
                                       then  "Old"
                                       else "Result");
                                    Is_Attribute := True;

                                 end if;
                              end if;

                              Current_CNT_Element := Insert_CNT_Element
                                (Name   => To_String (Part_Name),
                                 Entity => Part_Entity,
                                 Map    => (if Is_Attribute
                                            then Current_Attributes_Map
                                            else Current_Subfields_Map));

                   --  Note that Value is set even if it has already been set.
                   --  Overriding of value happens if a loop is unrolled (see
                   --  Gnat2Why.Expr.Loops.Wrap_Loop) and the VC for that the
                   --  counterexample was generated is for a  loop iteration.
                   --  In this case, there are both counterexample elements
                   --  for variables in an unrolling of the loop and a loop
                   --  iteration and these counterexample elements have the
                   --  same names and locations (but can have different
                   --  values). Note that in this case only the
                   --  counterexample elements for the loop iteration are
                   --  relevant for the proof. Counterexample elements are
                   --  reported in the order in  that the corresponding
                   --  variables are in generated why code and thus using the
                   --  last counterexample element with given Name ensures
                   --  the correct behavior.
                              if Var_Slice_Num = Slice_Count (Name_Parts) then
                                 Current_CNT_Element.Value :=
                                   To_Unbounded_String (Value);
                              end if;

                              Current_Subfields_Map :=
                                Current_CNT_Element.Fields;

                              Current_Attributes_Map :=
                                Current_CNT_Element.Attributes;
                           end;
                        end loop;
                     end;
                     <<Next_Model_Element>>
                  end loop;
               end Build_Variables_Info;

               procedure Build_Pretty_Line
                 (Variables : Variables_Info;
                  Pretty_Line_Cntexmp_Arr : out JSON_Array);
               --  Build pretty printed JSON array of counterexample elements.
               --  @Variables stores information about values and fields of
               --    variables at a single source code location (line).

               -----------------------
               -- Build_Pretty_Line --
               -----------------------

               procedure Build_Pretty_Line
                 (Variables : Variables_Info;
                  Pretty_Line_Cntexmp_Arr : out JSON_Array)
               is
                  type Name_And_Value is record
                     Name : Unbounded_String;
                     Value : Unbounded_String;
                  end record;
                  --  type of a pairs of unbounded strings, used to represent
                  --  the name and value of attributes.

                  package Names_And_Values is
                    new Ada.Containers.Doubly_Linked_Lists
                      (Element_Type => Name_And_Value);

                  function Get_CNT_Element_Value_And_Attributes
                    (CNT_Element : CNT_Element_Ptr;
                     Prefix : Unbounded_String;
                     Attributes : in out Names_And_Values.List)
                     return Unbounded_String;
                  --  Gets the string value of given variable, record field or
                  --  Attribute.
                  --  If the value is of record type, the returned value is
                  --  a record aggregate.
                  --  If the value should not be displayed in countereexample,
                  --  value "@not_display" is returned.
                  --  In addition, populate the list of attributes "Attributes"
                  --  of CNT_Element if any is found.

                  ---------------------------
                  -- Get_CNT_Element_Value --
                  ---------------------------

                  function Get_CNT_Element_Value_And_Attributes
                    (CNT_Element : CNT_Element_Ptr;
                     Prefix : Unbounded_String;
                     Attributes : in out Names_And_Values.List)
                     return Unbounded_String
                  is
                     Element_Type : Entity_Id;
                  begin

                     --  We first treat attributes
                     if not CNT_Element.Attributes.Is_Empty
                     then
                        for Att in CNT_Element.Attributes.Iterate loop
                           declare
                              New_Prefix : constant Unbounded_String :=
                                Prefix & "'" & CNT_Elements.Key (Att);

                              Attr_Value : constant Unbounded_String :=
                                Get_CNT_Element_Value_And_Attributes
                                  (CNT_Elements.Element (Att),
                                   New_Prefix,
                                   Attributes);
                           begin
                              if Attr_Value /= Dont_Display
                              then
                                 Attributes.Append ((New_Prefix, Attr_Value));
                              end if;
                           end;
                        end loop;
                     end if;

                     --  Now that the attributes are dealt with
                     --  Check if we've got any field, if not we return the
                     --  value of the node
                     if CNT_Element.Fields.Is_Empty then
                        return (if CNT_Element.Value = "true"
                                then To_Unbounded_String ("True")
                                elsif CNT_Element.Value = "false"
                                then To_Unbounded_String ("False")
                                else CNT_Element.Value);
                     end if;

                     --  If we've got fields, we're dealing with a record:
                     --  we know that CNT_Element.Entity is present
                     Element_Type := Etype (CNT_Element.Entity);

                     --  Check whether the type can have fields or
                     --  discriminants

                     if not Is_Concurrent_Type (Element_Type)
                       and then
                         not Is_Incomplete_Or_Private_Type (Element_Type)
                       and then not Is_Record_Type (Element_Type)
                       and then not Has_Discriminants (Element_Type)
                     then
                        return Dont_Display;
                     end if;

                     --  Create aggregate representing the value of
                     --  CNT_Element
                     --  Go through all fields of CNT_Element.
                     --  To give the fields in the order of their
                     --  declaration in the type of the CNT_Element
                     --  (CNT_Element_Type), iterate through components
                     --  of CNT_Element_Type

                     declare
                        function Get_Fields_Descr_Declared
                          return Natural;
                        --  Return the number of declared fields and
                        --  descriminants of the (record) type of the
                        --  current CNT_Element.

                        -------------------------------
                        -- Get_Fields_Descr_Declared --
                        -------------------------------

                        function Get_Fields_Descr_Declared return Natural
                        is
                           Res : Natural := 0;
                           Comp : Entity_Id :=
                             First_Component_Or_Discriminant
                               (Element_Type);
                        begin
                           while Present (Comp) loop
                              Res := Res + 1;
                              Next_Component (Comp);
                           end loop;

                           return Res;
                        end Get_Fields_Descr_Declared;

                        Fields_Discrs_Collected : constant Natural :=
                          Natural (Length (CNT_Element.Fields.all));
                        Fields_Discrs_Declared : constant Natural :=
                          Get_Fields_Descr_Declared;
                        Fields_Discrs_With_Value : Natural := 0;
                        Decl_Field_Discr : Entity_Id :=
                          First_Component_Or_Discriminant
                            (Element_Type);
                        Is_Before : Boolean := False;
                        Value : Unbounded_String :=
                          To_Unbounded_String ("(");
                     begin

                        --  If the record type of the value has no fields
                        --  and discriminats or if there were no
                        --  counterexample values for fields and
                        --  discriminants of the processed value
                        --  collected, do not display the value
                        if Fields_Discrs_Collected = 0 or else
                          Fields_Discrs_Declared = 0
                        then
                           return Dont_Display;
                        end if;

                        while Present (Decl_Field_Discr) loop
                           declare
                              Field_Descr_Name : constant String :=
                                Source_Name (Decl_Field_Discr);
                              Field_Descr : constant Cursor :=
                                Find (CNT_Element.Fields.all,
                                      Field_Descr_Name);
                           begin
                              if Has_Element (Field_Descr) or else
                                Fields_Discrs_Declared -
                                Fields_Discrs_Collected <= 1
                              then
                                 declare
                                    Field_Descr_Val : constant Unbounded_String
                                      :=
                                      (if Has_Element (Field_Descr)
                                       then
                                         Get_CNT_Element_Value_And_Attributes
                                           (Element (Field_Descr),
                                            Prefix & "." & Field_Descr_Name,
                                            Attributes)
                                       else To_Unbounded_String ("?"));
                                 begin
                                    if Field_Descr_Val /= Dont_Display
                                    then
                                       Append (Value,
                                               (if Is_Before then ", "
                                                else "") &
                                                 Field_Descr_Name &
                                                 " => " &
                                                 Field_Descr_Val);
                                       Is_Before := True;
                                       if Has_Element (Field_Descr) then
                                          Fields_Discrs_With_Value :=
                                            Fields_Discrs_With_Value + 1;
                                       end if;
                                    end if;
                                 end;
                              end if;
                              Next_Component (Decl_Field_Discr);
                           end;
                        end loop;

                        --  If there are no fields and discriminants of
                        --  the processed value with values that can be
                        --  displayed do not display the value (this can
                        --  happen if there were collected fields or
                        --  discrinants, but there values should not be
                        --  displayed)
                        if Fields_Discrs_With_Value = 0 then
                           return Dont_Display;
                        end if;

                        --  If there are more than one field that is not
                        --  mentioned in the counterexample, summarize
                        --  them using the field others
                        if Fields_Discrs_Declared -
                          Fields_Discrs_Collected > 1
                        then
                           Append (Value,
                                   (if Is_Before then ", " else "") &
                                     "others => ?");
                        end if;
                        Append (Value, ")");

                        return Value;
                     end;
                  end Get_CNT_Element_Value_And_Attributes;

                  Var_Name_Cursor : Vars_List.Cursor :=
                    Vars_List.First (Variables.Variables_Order);

               --  Start of processing for Build_Pretty_Line

               begin
                  Pretty_Line_Cntexmp_Arr := Empty_Array;
                  while Vars_List.Has_Element (Var_Name_Cursor) loop
                     declare
                        Var_Name : constant Unbounded_String :=
                          Vars_List.Element (Var_Name_Cursor);
                        Variable : Cursor :=
                          Find (Variables.Variables_Map,
                                To_String (Var_Name));
                        Attributes : Names_And_Values.List :=
                          Names_And_Values.Empty_List;
                        Var_Value : constant Unbounded_String :=
                          Get_CNT_Element_Value_And_Attributes
                            (Element (Variable),
                             Var_Name,
                             Attributes);

                        procedure Add_CNT (Name, Value : Unbounded_String);
                        --  Append a variable cnt to Pretty_Line_Cntexmp_Arr

                        procedure Add_CNT (Name, Value : Unbounded_String)
                        is
                           Pretty_Var : constant JSON_Value := Create_Object;
                        begin
                           --  If the value of the variable should not be
                           --  displayed in the counterexample, do not display
                           --  the variable.
                           if Value /= Dont_Display then
                              Set_Field (Pretty_Var, "name", Create (Name));
                              Set_Field (Pretty_Var, "value", Create (Value));
                              Set_Field (Pretty_Var, "kind",
                                         Create ("variable"));

                              Append (Pretty_Line_Cntexmp_Arr, Pretty_Var);
                           end if;
                        end Add_CNT;
                     begin
                        Add_CNT (Var_Name, Var_Value);

                        for Att of Attributes loop
                           Add_CNT (Att.Name, Att.Value);
                        end loop;

                        Next (Variable);
                     end;
                     Var_Name_Cursor := Vars_List.Next (Var_Name_Cursor);
                  end loop;
               end Build_Pretty_Line;

               Variables : Variables_Info;
               Pretty_Line_Cntexmp_Arr : JSON_Array := Empty_Array;

            --  Start of processing for Create_Pretty_Line

            begin
               Build_Variables_Info (Get (Line_Cntexmp), Variables);

               if not Is_Empty (Variables.Variables_Map) then
                  Build_Pretty_Line (Variables, Pretty_Line_Cntexmp_Arr);

                  --  Add the counterexample line only if there are some
                  --  pretty printed counterexample elements
                  if Pretty_Line_Cntexmp_Arr /= Empty_Array then
                     Set_Field (Pretty_File_Cntexmp,
                                Line,
                                Create (Pretty_Line_Cntexmp_Arr));
                  end if;
               end if;
            end Create_Pretty_Line;

            Pretty_File_Cntexmp : JSON_Value := Create_Object;

         --  Start of processing for Create_Pretty_File

         begin
            Gen_JSON_Object
              (File_Cntexmp, Create_Pretty_Line'Access, Pretty_File_Cntexmp);
            if File'Length >= 4 and then
              (File ((File'Last - 2) .. File'Last) in "adb" | "ads")
            then
               Set_Field (Pretty_Cntexmp, File, Pretty_File_Cntexmp);
            end if;
         end Create_Pretty_File;

         function Remap_VC_Info (Cntexmp : JSON_Value;
                                 VC_File : String;
                                 VC_Line : Logical_Line_Number)
                                 return JSON_Value;
         --  Remap information related to the construct that triggers VC to the
         --  location of this construct.
         --  In Cntexmp, this information is mapped to the field "vc_line" of
         --  the JSON object representing the file where the construct that
         --  triggers VC is located.

         -------------------
         -- Remap_VC_Info --
         -------------------

         function Remap_VC_Info (Cntexmp : JSON_Value;
                                 VC_File : String;
                                 VC_Line : Logical_Line_Number)
                                 return JSON_Value
         is

            procedure Remove_VC_Line (New_Cntexmp : in out JSON_Value;
                                      File_Name : UTF8_String;
                                      Orig_File : JSON_Value);
            --  Create a copy of Orig_File without information related to the
            --  construct triggering VC and extend New_Cntexmp with a mapping
            --  from File_Name to this copy.

            --------------------
            -- Remove_VC_Line --
            --------------------

            procedure Remove_VC_Line (New_Cntexmp : in out JSON_Value;
                                      File_Name : UTF8_String;
                                      Orig_File : JSON_Value)
            is
               procedure Add_Non_VC_Line (New_File : in out JSON_Value;
                                          Line_Num : UTF8_String;
                                          Line : JSON_Value);

               ---------------------
               -- Add_Non_VC_Line --
               ---------------------

               procedure Add_Non_VC_Line (New_File : in out JSON_Value;
                                          Line_Num : UTF8_String;
                                          Line : JSON_Value)
               is
               begin
                  if Line_Num /= "vc_line" then
                     Set_Field (New_File, Line_Num, Line);
                  end if;
               end Add_Non_VC_Line;

               New_File : JSON_Value := Create_Object;

            --  Start of processing for Remove_VC_Line

            begin
               Gen_JSON_Object (Orig_File, Add_Non_VC_Line'Access, New_File);
               Set_Field (New_Cntexmp, File_Name, New_File);
            end Remove_VC_Line;

            Cntexmp_File : constant JSON_Value :=
              JSON_Get_Opt (Cntexmp, VC_File, Create_Object);
            Cntexmp_VC_Line : constant JSON_Array :=
              (if Has_Field (Cntexmp_File, "vc_line")
               then Get (Get (Cntexmp_File, "vc_line"))
               else Empty_Array);
            Remapped_Cntexmp : JSON_Value := Create_Object;
            VC_Line_Str : constant String := Trim (VC_Line'Img, Left);

         --  Start of processing for Remap_VC_Info

         begin
            --  Remove information related to the construct triggering VC
            Gen_JSON_Object (Cntexmp, Remove_VC_Line'Access, Remapped_Cntexmp);

            --  Map the information related to the construct triggering VC to
            --  the location of that construct.
            Set_Field (JSON_Get_Opt (Remapped_Cntexmp, VC_File, Create_Object),
                       VC_Line_Str,
                       Cntexmp_VC_Line);

            return Remapped_Cntexmp;
         end Remap_VC_Info;

         File : constant String := File_Name (VC_Loc);
         Line : constant Logical_Line_Number :=
           Get_Logical_Line_Number (VC_Loc);
         Remapped_Cntexmp : constant JSON_Value :=
           Remap_VC_Info (Cntexmp, File, Line);
         Pretty_Cntexmp : JSON_Value := Create_Object;

      --  Start of processing for Create_Pretty_Cntexmp

      begin
         Gen_JSON_Object (Remapped_Cntexmp,
                          Create_Pretty_File'Access,
                          Pretty_Cntexmp);

         return Pretty_Cntexmp;
      end Create_Pretty_Cntexmp;

      ---------------------------
      -- Get_Cntexmp_One_Liner --
      ---------------------------

      function Get_Cntexmp_One_Liner
        (Cntexmp : JSON_Value; VC_Loc : Source_Ptr) return String
      is
         function Get_Cntexmp_Line_Str
           (Cntexmp_Line : JSON_Array) return String;

         --------------------------
         -- Get_Cntexmp_Line_Str --
         --------------------------

         function Get_Cntexmp_Line_Str
           (Cntexmp_Line : JSON_Array) return String
         is
            Cntexmp_Line_Str : Unbounded_String := Null_Unbounded_String;

            procedure Add_Cntexmp_Element
              (Add_Cntexmp_Element : JSON_Value);

            -------------------------
            -- Add_Cntexmp_Element --
            -------------------------

            procedure Add_Cntexmp_Element
              (Add_Cntexmp_Element : JSON_Value)
            is
               Name  : constant String := Get (Add_Cntexmp_Element, "name");
               Value : constant JSON_Value :=
                 Get (Add_Cntexmp_Element, "value");
               Kind  : constant String := Get (Add_Cntexmp_Element, "kind");
               Element : constant String := Name &
                 (if Kind = "error_message" then "" else " = " & Get (Value));
            begin
               if Cntexmp_Line_Str /= "" then
                  Append (Cntexmp_Line_Str, " and ");
               end if;
               Append (Cntexmp_Line_Str, Element);
            end Add_Cntexmp_Element;

         begin
            for I in Positive range 1 .. Length (Cntexmp_Line) loop
               Add_Cntexmp_Element (Get (Cntexmp_Line, I));
            end loop;

            return To_String (Cntexmp_Line_Str);
         end Get_Cntexmp_Line_Str;

         File : constant String := File_Name (VC_Loc);
         Line : constant Logical_Line_Number :=
           Get_Logical_Line_Number (VC_Loc);
         Line_Str : constant String := Trim (Line'Img, Left);
         Cntexmp_File : constant JSON_Value :=
           JSON_Get_Opt (Cntexmp, File, Create_Object);
         Cntexmp_Line : constant JSON_Array :=
           (if Has_Field (Cntexmp_File, Line_Str)
            then Get (Get (Cntexmp_File, Line_Str))
            else Empty_Array);
      begin
         return Get_Cntexmp_Line_Str (Cntexmp_Line);
      end Get_Cntexmp_One_Liner;

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
         if Is_Proved then
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

      Msg2 : constant String     := Compute_Message (Msg, N);
      Slc  : constant Source_Ptr := Compute_Sloc (N, Place_First);

      Pretty_Cntexmp  : constant JSON_Value :=
        Create_Pretty_Cntexmp (Cntexmp, Slc);
      One_Liner : constant String :=
        (if Is_Empty (Pretty_Cntexmp) then ""
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
               Msg_Id := Print_Regular_Msg (Msg3, Slc, Severity);
            end if;
         when Info_Kind =>
            if Report_Mode /= GPR_Fail then
               Msg_Id := Print_Regular_Msg (Msg3, Slc, Severity);
            end if;
         when Error_Kind | Warning_Kind =>
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
         Tracefile   => Tracefile,
         Cntexmp     => Pretty_Cntexmp,
         VC_File     => VC_File,
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
      for Index in S'Range loop
         if S (Index) in '%' | '$' | '{' | '*' | '&' | '#' |
                         '}' | '@' | '^' | '>' | '!' | '?' |
                         '<' | '`' | ''' | '\' | '|'
           or else Is_Upper_Case_Letter (S (Index))
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
        Unit_Name & "__flow__" & Image (File_Counter, 1) & ".trace";
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

   function Msg_Severity_To_String (Severity : Msg_Severity) return String is
     ((case Severity is
          when Error_Kind        => "error",
          when Warning_Kind      => "warning",
          when Info_Kind         => "info",
          when High_Check_Kind   => "high",
          when Medium_Check_Kind => "medium",
          when Low_Check_Kind    => "low"));

   ------------------
   -- Add_Json_Msg --
   ------------------

   procedure Add_Json_Msg
     (Suppr       : String_Id;
      Tag         : String;
      Severity    : Msg_Severity;
      Slc         : Source_Ptr;
      Msg_List    : in out GNATCOLL.JSON.JSON_Array;
      E           : Entity_Id;
      Msg_Id      : Message_Id;
      Tracefile   : String := "";
      Cntexmp     : JSON_Value := GNATCOLL.JSON.Create_Object;
      VC_File     : String := "";
      How_Proved  : String := "";
      Stats       : JSON_Value := GNATCOLL.JSON.Create_Object;
      Editor_Cmd  : String := "")
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
      Set_Field (Value, "entity", To_JSON (Entity_To_Subp (E)));

      if Tracefile /= "" then
         Set_Field (Value, "tracefile", Tracefile);
      end if;

      if not Is_Empty (Cntexmp) then
         Set_Field (Value, "cntexmp", Cntexmp);
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

      if How_Proved /= "" then
         Set_Field (Value, "how_proved", How_Proved);
      end if;

      if not Is_Empty (Stats) then
         Set_Field (Value, "stats", Stats);
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
            when Info_Kind         => "info: ?",
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
                     Append (R, "constant with");
                     if not Has_Variable_Input (F) then
                        Append (R, "out");
                     end if;
                     Append (R, " variable input ");
                     Append_Quote;
                     Append (R, Flow_Id_To_String (F));
                  elsif Is_Constituent (F) then
                     Append_Quote;
                     Append (R, Flow_Id_To_String (F));
                     Append_Quote;
                     Append (R, " constituent of ");
                     Append_Quote;
                     declare
                        Encaps_State : constant Node_Id :=
                          Encapsulating_State (Get_Direct_Mapping_Id (F));
                        Encaps_Scope : constant Node_Id :=
                          Scope (Encaps_State);
                     begin
                        --  If scopes of the abstract state and its constituent
                        --  differ then prefix the name of the abstract state
                        --  with its immediate scope.
                        if Encaps_Scope /= Scope (Get_Direct_Mapping_Id (F))
                        then
                           Get_Name_String (Chars (Encaps_Scope));
                           Adjust_Name_Case (Sloc (Encaps_Scope));

                           Append (R, Name_Buffer (1 .. Name_Len) & ".");
                        end if;

                        Get_Name_String (Chars (Encaps_State));
                        Adjust_Name_Case (Sloc (Encaps_State));

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
                     F_Name_String : constant String := To_String (F.Name);
                  begin
                     if F_Name_String = "__HEAP" then
                        Append (R, "the heap");
                     else
                        declare
                           Index : Positive := F_Name_String'First;
                        begin
                           --  Replace __ with . in the magic string.
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

         if Present (F3)
           and then F3.Kind in Direct_Mapping | Record_Field
           and then Is_Entity_And_Has_Warnings_Off (Get_Direct_Mapping_Id (F3))
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
