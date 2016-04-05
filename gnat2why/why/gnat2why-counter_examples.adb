------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              G N A T 2 W H Y _ C O U N T E R _ E X A M P L E S           --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2016, AdaCore                        --
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
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers.Indefinite_Ordered_Maps;
with Ada.Containers.Doubly_Linked_Lists;
with Ada.Containers.Ordered_Sets;
with Ada.Strings;               use Ada.Strings;
with Ada.Strings.Fixed;         use Ada.Strings.Fixed;
with Ada.Strings.Unbounded;     use Ada.Strings.Unbounded;
with Atree;                     use Atree;
with Einfo;                     use Einfo;
with GNAT;                      use GNAT;
with GNAT.String_Split;
with Gnat2Why.Counter_Examples; use Gnat2Why.Counter_Examples;
with Sinfo;                     use Sinfo;
with Sinput;                    use Sinput;
with SPARK_Util;                use SPARK_Util;

package body Gnat2Why.Counter_Examples is

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
                 Element_Type => CNT_Element_Ptr);

            type CNT_Element_Map_Ptr is access all
              CNT_Elements.Map;

            package Vars_List is
              new Ada.Containers.Ordered_Sets
                (Element_Type => Unbounded_String);

            --  Represents variables at given source code location.
            type Variables_Info is record
               Variables_Order : Vars_List.Set;
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

            function Print_CNT_Element_Debug (El : CNT_Element) return String;
            --  Debug function, print a CNT_Element without any processing

            -----------------------------
            -- Print_CNT_Element_Debug --
            -----------------------------

            function Print_CNT_Element_Debug (El : CNT_Element) return String
            is
               R : Unbounded_String := "[ " & El.Value & " | ";
            begin
               for F in El.Fields.Iterate loop
                  Append
                    (R,
                     "<F- " & CNT_Elements.Key (F) & " = " &
                     Print_CNT_Element_Debug (CNT_Elements.Element (F).all) &
                     " -F>");
               end loop;

               for F in El.Attributes.Iterate loop
                  Append
                    (R,
                     "<A- " & CNT_Elements.Key (F) & " = " &
                     Print_CNT_Element_Debug (CNT_Elements.Element (F).all)
                     & " -A>");
               end loop;

               Append (R, " ]");

               return To_String (R);
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
                                             In_Present
                                               (Parent (Element_Decl));

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
                                 Vars_List.Include
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

                           --  Note that Value is set even if it has already
                           --  been set. Overriding of value happens if a loop
                           --  is unrolled (see Gnat2Why.Expr.Loops.Wrap_Loop)
                           --  and the VC for that the counterexample was
                           --  generated is for a loop iteration. In this
                           --  case, there are both counterexample elements
                           --  for variables in an unrolling of the loop and a
                           --  loop iteration and these counterexample elements
                           --  have the same names and locations (but can
                           --  have different values). Note that in this
                           --  case only the counterexample elements for the
                           --  loop iteration are relevant for the proof.
                           --  Counterexample elements are reported in the
                           --  order in that the corresponding variables are
                           --  in generated why code and thus using the last
                           --  counterexample element with given Name ensures
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

end Gnat2Why.Counter_Examples;
