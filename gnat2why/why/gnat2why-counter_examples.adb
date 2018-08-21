------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              G N A T 2 W H Y _ C O U N T E R _ E X A M P L E S           --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                    Copyright (C) 2016-2018, AdaCore                      --
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

with Ada.Containers;            use Ada.Containers;
with Ada.Containers.Doubly_Linked_Lists;
with Ada.Containers.Ordered_Maps;
with Ada.Containers.Ordered_Sets;
with Ada.Containers.Indefinite_Ordered_Maps;
with Ada.Strings;               use Ada.Strings;
with Ada.Strings.Unbounded;     use Ada.Strings.Unbounded;
with Ce_Interval_Sets;
with Ce_Pretty_Printing;        use Ce_Pretty_Printing;
with Common_Containers;         use Common_Containers;
with Flow_Refinement;           use Flow_Refinement;
with Flow_Types;                use Flow_Types;
with GNAT;                      use GNAT;
with GNAT.String_Split;         use GNAT.String_Split;
with Gnat2Why.CE_Utils;         use Gnat2Why.CE_Utils;
with Gnat2Why.Tables;           use Gnat2Why.Tables;
with Gnat2Why.Util;             use Gnat2Why.Util;
with Namet;                     use Namet;
with Nlists;                    use Nlists;
with Sinput;                    use Sinput;
with Snames;                    use Snames;
with SPARK_Annotate;            use SPARK_Annotate;
with SPARK_Atree;               use SPARK_Atree;
with SPARK_Atree.Entities;      use SPARK_Atree.Entities;
with SPARK_Util;                use SPARK_Util;
with SPARK_Util.Types;          use SPARK_Util.Types;
with String_Utils;              use String_Utils;
with Uintp;                     use Uintp;

package body Gnat2Why.Counter_Examples is

   Dont_Display : constant Unbounded_String :=
     To_Unbounded_String ("@not_display");

   function Remap_VC_Info
     (Cntexmp : Cntexample_File_Maps.Map;
      VC_File : String;
      VC_Line : Natural)
      return Cntexample_File_Maps.Map;
   --  Map counterexample information related to the current VC to the
   --  location of the check in the Ada file.
   --  In Cntexmp, this information is mapped to the field "vc_line" of the
   --  JSON object representing the file where the construct is located.

   function Remove_Irrelevant_Branches
     (Cntexmp : Cntexample_File_Maps.Map)
      return Cntexample_File_Maps.Map;
   --  Remove counterexample branches that are not taken

   function Is_Ada_File_Name (File : String) return Boolean;
   --  check if the filename is an Ada
   --  ??? This check is wrong, need to get rid of it

   function Is_Uninitialized
     (Element_Decl : Entity_Id;
      Element_File : String;
      Element_Line : Natural)
      return Boolean
   with Pre => Nkind (Element_Decl) in N_Entity;
   --  Return True if the counterexample element with given declaration at
   --  given position is uninitialized.

   type CNT_Element (<>);
   type CNT_Element_Ptr is access all CNT_Element;

   package CNT_Elements is
     new Ada.Containers.Ordered_Maps
       (Key_Type     => Entity_Id,
        Element_Type => CNT_Element_Ptr);

   type CNT_Element_Map_Ptr is access all CNT_Elements.Map;

   package CNT_Attributes is
     new Ada.Containers.Indefinite_Ordered_Maps
       (Key_Type     => String,
        Element_Type => CNT_Element_Ptr);

   type CNT_Attributes_Map_Ptr is access all CNT_Attributes.Map;

   type Var_Info is record
      Name : Unbounded_String;
      Id   : Entity_Id;
   end record;
   --  Variables are stored in alphabetical order. Keep the entity id in case
   --  there are several variables with the same name.

   function "<" (X, Y : Var_Info) return Boolean is
     (X.Name < Y.Name or else (X.Name = Y.Name and then X.Id < Y.Id));
   function "=" (X, Y : Var_Info) return Boolean is (X.Id = Y.Id);

   package Var_Lists is new Ada.Containers.Ordered_Sets (Var_Info);

   type Variables_Info is record
      Variables_Order : Var_Lists.Set;
      --  Vector of variable entities in the order in that variables should be
      --  displayed.

      Variables_Map : aliased CNT_Elements.Map;
      --  Map from variable entities to information about these variables. This
      --  includes values of variables, informations about possible record
      --  fields and informations about possible attributes.
   end record;
   --  Represents variables at given source code location

   type CNT_Element is record
      Entity     : Entity_Id;
      --  The corresponding element of SPARK AST

      Attributes : CNT_Attributes_Map_Ptr;
      Fields     : CNT_Element_Map_Ptr;
      Value      : Cntexmp_Value_Ptr;
      Val_Str    : Unbounded_String;
   end record;
   --  Represents information about the element of a counter
   --  example. An element can be either:
   --  * a variable/field/attribute of a record type, in which case
   --    - Value = "@not_display",
   --    - Fields contains the CNT_Element of some/all of its fields
   --    - Attributes may contain info on its attributes.
   --  * a "flat" variable/field/attribute, in which case
   --    - Value is set to the counter example value
   --    - Fields is empty
   --    - and Attributes may contain info on its attributes.

   type Component_Loc_Info is record
      Type_Ent : Entity_Id;
      Sloc     : Source_Ptr;
   end record;
   --  A location information for a component contains the type in which the
   --  component is declared first and the location of this first declaration.

   function Get_Loc_Info (Comp : Entity_Id) return Component_Loc_Info is
     ((Type_Ent => Original_Declaration (Comp),
       Sloc     =>
          Sloc
         (Search_Component_In_Type (Original_Declaration (Comp), Comp))));
   --  Construct the location information of a record component or
   --  discriminant.

   function "<" (X, Y : Component_Loc_Info) return Boolean is
     ((X.Type_Ent /= Y.Type_Ent and then Is_Ancestor (X.Type_Ent, Y.Type_Ent))
      or else (X.Type_Ent = Y.Type_Ent
               and then
                 (Get_Physical_Line_Number (X.Sloc) <
                      Get_Physical_Line_Number (Y.Sloc)
                  or else (Get_Physical_Line_Number (X.Sloc) =
                             Get_Physical_Line_Number (Y.Sloc)
                           and then Get_Column_Number (X.Sloc) <
                             Get_Column_Number (Y.Sloc)))));
   --  Order on location information. A component F1 is declared first than
   --  another F2 if F1 is declared in an ancestor of the type in which F2 is
   --  declared, or if they are declared in the same type and F1 occurs before
   --  in the source code.

   package Ordered_Sloc_Map is new Ada.Containers.Ordered_Maps
     (Key_Type     => Component_Loc_Info,
      Element_Type => Unbounded_String,
      "<"          => "<");
   --  Map from sloc to strings, used to output component of record values in
   --  correct order.

   procedure Build_Pretty_Line
     (Variables               : Variables_Info;
      Pretty_Line_Cntexmp_Arr : out Cntexample_Elt_Lists.List);
   --  Build pretty printed JSON array of counterexample elements.
   --  @Variables stores information about values and fields of
   --    variables at a single source code location (line).

   procedure Build_Variables_Info
     (File             : String;
      Line             : Natural;
      Line_Cntexmp_Arr : Cntexample_Elt_Lists.List;
      Variables        : in out Variables_Info);
   --  Build a structure holding the informations associated to the
   --  counterexample at a single source code location.
   --  This structure associates to each variable mentioned in the
   --  counterexample a CNT_Element gathering the infos given in the
   --  counter example (fields if any, attributes and associated value(s)).
   --  @param Line_Cntexmp_Arr counterexample model elements at a
   --    single source code location (line)
   --  @param Variables stores information about values, fields
   --    and or attributes of variables at a single source code
   --    location.

   function Print_CNT_Element_Debug (El : CNT_Element) return String;
   --  Debug function, print a CNT_Element without any processing

   function Refine
     (Cnt_Value : Cntexmp_Value_Ptr;
      AST_Node  : Entity_Id)
      return Unbounded_String;
   --  This function takes a value from Why3 Cnt_Value and converts it into a
   --  suitable string for the corresponding entity in GNAT AST node AST_Node.
   --  Example: (97, Character_entity) -> "'a'"

   function Refine_Attribute (Cnt_Value : Cntexmp_Value_Ptr)
                              return Unbounded_String;
   --  Refine CNT_Value assuming it is an integer

   function Refine_Iterator_Value
     (Cnt_Value : Cntexmp_Value_Ptr;
      Quant_Var : Entity_Id) return Unbounded_String;
   --  Refine CNT_Value for "for of" quantification iterators

   ------------
   -- Refine --
   ------------

   function Refine
     (Cnt_Value : Cntexmp_Value_Ptr;
      AST_Node  : Entity_Id)
      return Unbounded_String
   is
      function Compile_Time_Known_And_Constant (E : Entity_Id) return Boolean;
      --  This is used to know if something is compile time known and has
      --  the keyword constant on its definition. Internally, it calls
      --  Compile_Time_Known_Value_Or_Aggr.

      function Refine_Aux
        (Cnt_Value : Cntexmp_Value_Ptr;
         AST_Type  : Entity_Id;
         Is_Index  : Boolean := False)
         return Unbounded_String;
      --  Mutually recursive function with the local Refine_Value, which trims
      --  space on both ends of the result.

      function Refine_Array
        (Arr_Indices  : Cntexmp_Value_Array.Map;
         Arr_Others   : Cntexmp_Value_Ptr;
         Arr_Indice   : Entity_Id;
         Element_Type : Entity_Id)
         return Unbounded_String
      with Pre => Is_Discrete_Type (Retysp (Etype (Arr_Indice)))
                    and then
                  Is_Type (Element_Type);

      function Refine_Value
        (Cnt_Value : Cntexmp_Value_Ptr;
         AST_Type  : Entity_Id;
         Is_Index  : Boolean := False)
         return Unbounded_String;
      --  Mutually recursive function with the local Refine, which does the
      --  actual conversion.

      function Replace_Question_Mark (S : Unbounded_String)
                                      return Unbounded_String;
      --  This replaces empty string by question mark in some cases where it is
      --  needed.

      -------------------------------------
      -- Compile_Time_Known_And_Constant --
      -------------------------------------

      function Compile_Time_Known_And_Constant (E : Entity_Id) return Boolean
      is
      begin
         if Ekind (E) = E_Constant then
            declare
               Decl : constant Node_Id := Enclosing_Declaration (E);
               Expr : constant Node_Id := Expression (Decl);
            begin
               return Present (Expr)
                 and then Compile_Time_Known_Value_Or_Aggr (Expr);
            end;
         end if;

         return False;
      end Compile_Time_Known_And_Constant;

      function Print_Float (Cnt_Value : Cntexmp_Value)
                            return Unbounded_String;

      ----------------
      -- Refine_Aux --
      ----------------

      function Refine_Aux
        (Cnt_Value : Cntexmp_Value_Ptr;
         AST_Type  : Entity_Id;
         Is_Index  : Boolean := False)
         return Unbounded_String
      is

         Why3_Type : constant Cntexmp_Type := Cnt_Value.all.T;
      begin
         case Why3_Type is
            when Cnt_Integer =>

               --  Necessary for some types that makes boolean be translated to
               --  integers like: "subype only_true := True .. True".

               if Is_Boolean_Type (AST_Type) then
                  return To_Unbounded_String (Cnt_Value.I /= "0");

               elsif Is_Enumeration_Type (AST_Type) then
                  declare
                     Value : constant Uint := UI_From_String
                         (To_String (Cnt_Value.I));

                     --  Call Get_Enum_Lit_From_Pos to get a corresponding
                     --  enumeration entity.

                     Enum  : Entity_Id;

                  begin
                     --  Initialization of Enum can raise Constraint_Error if
                     --  there is no literal value for the position.

                     Enum := Get_Enum_Lit_From_Pos (AST_Type, Value);

                     --  Special case for characters, which are defined in the
                     --  standard unit Standard.ASCII, and as such do not have
                     --  a source code representation.

                     if Is_Character_Type (AST_Type) then
                        --  Call Get_Unqualified_Decoded_Name_String to get a
                        --  correctly printed character in Name_Buffer.

                        Get_Unqualified_Decoded_Name_String (Chars (Enum));

                        --  The call to Get_Unqualified_Decoded_Name_String
                        --  set Name_Buffer to '<char>' where <char> is the
                        --  character we are interested in. Just retrieve it
                        --  directly at Name_Buffer(2).

                        return "'" & To_Unbounded_String
                          (Char_To_String_Representation
                             (Name_Buffer (2))) & "'";

                        --  For all enumeration types that are not character,
                        --  call Get_Enum_Lit_From_Pos to get a corresponding
                        --  enumeratio n entity, then Source_Name to get a
                        --  correctly capitalized enumeration value.

                     else
                        return To_Unbounded_String (Source_Name (Enum));
                     end if;

                     --  An exception is raised by Get_Enum_Lit_From_Pos
                     --  if the position Value is outside the bounds of the
                     --  enumeration. In such a case, return the raw integer
                     --  returned by the prover.

                  exception
                     when Constraint_Error =>
                        if Is_Index then
                           return Null_Unbounded_String;
                        else
                           return Cnt_Value.I;
                        end if;
                  end;

                  --  Cvc4 returns Floating_point value with integer type. We
                  --  don't want to print those.

               elsif Is_Floating_Point_Type (AST_Type) then
                  return Null_Unbounded_String;

               elsif Is_Fixed_Point_Type (AST_Type) then
                  return To_Unbounded_String
                    (Print_Fixed (Small_Value (AST_Type),
                     To_String (Cnt_Value.I)));

               --  Only integer types are expected in that last case

               else
                  pragma Assert (Is_Discrete_Type (AST_Type));
                  return Cnt_Value.I;
               end if;

            when Cnt_Boolean =>
               return To_Unbounded_String (Cnt_Value.Bo);

            when Cnt_Bitvector =>

               --  Boolean are translated into bitvector of size 1 for CVC4
               --  because it fails to produce a model when booleans are used
               --  inside translated arrays_of_records.

               if Is_Boolean_Type (AST_Type) then
                  return To_Unbounded_String (Cnt_Value.B /= "0");
               end if;

               return Cnt_Value.B;

            when Cnt_Decimal =>
               return Cnt_Value.D;

            when Cnt_Float =>

               pragma Assert (Is_Floating_Point_Type (AST_Type));
               return Print_Float (Cnt_Value.all);

            when Cnt_Unparsed =>
               return Cnt_Value.U;

            when Cnt_Record =>

               --  AST_Type is of record type
               declare
                  Mfields       : constant Cntexmp_Value_Array.Map :=
                    Cnt_Value.Fi;
                  S             : Unbounded_String :=
                    To_Unbounded_String ("(");

                  AST_Basetype  : constant Entity_Id :=
                    Retysp (AST_Type);
                  Check_Count   : Integer := 0;
                  Fields        : constant Integer :=
                    Count_Why_Visible_Regular_Fields (AST_Basetype) +
                    Count_Discriminants (AST_Basetype);

               begin

                  Fields_Loop :
                  for Cursor in Mfields.Iterate loop
                     declare
                        Mfield       : constant Cntexmp_Value_Ptr :=
                          Cntexmp_Value_Array.Element (Cursor);
                        Key_Field    : constant String :=
                          Cntexmp_Value_Array.Key (Cursor);
                        Field_Entity : constant Entity_Id :=
                          Get_Entity_Id (True, Key_Field);
                     begin
                        --  There are two cases:
                        --  - discriminant -> we always include the field
                        --    corresponding to discriminants because they are
                        --    inherited by subtyping.
                        --    The current design enforce that the discriminant
                        --    is part of the AST_Basetype.
                        --  - components -> some components can be hidden by
                        --    subtyping. But, in Why3, any ancestor type
                        --    with the same field can be used. So,
                        --    counterexamples can have more components than
                        --    are actually defined in the AST_basetype.

                        if Present (Field_Entity) and then
                          (Ekind (Field_Entity) = E_Discriminant
                           or else
                           Is_Visible_In_Type (AST_Basetype,
                                               Field_Entity))
                        then
                           declare
                              Field_Type : constant Entity_Id :=
                                Retysp (Etype (Field_Entity));
                              Field_Name : constant String :=
                                Source_Name (Field_Entity);
                           begin
                              if Check_Count > 0 then
                                 Append (S, ", ");
                              end if;

                              Check_Count := Check_Count + 1;

                              Append (S, Field_Name & " => " &
                                        Replace_Question_Mark
                                        (Refine_Aux (Mfield, Field_Type)));
                           end;
                        end if;
                     end;

                  end loop Fields_Loop;

                  Append (S,
                          (if Check_Count /= Fields then
                             (if Check_Count > 0 then
                                 ", others => ?)"
                              else
                                 "others => ?)")
                           else ")"));

                  return S;
               end;

            --  This case only happens when the why3 counterexamples are
            --  incorrect. Ideally, this case should be removed but it
            --  still happens in practice.

            when Cnt_Invalid =>
               return Cnt_Value.S;

            when Cnt_Array =>
               pragma Assert (Is_Array_Type (AST_Type));
               declare
                  Element_Type : constant Entity_Id :=
                    Retysp (Component_Type (AST_Type));
               begin
                  return Refine_Array (Cnt_Value.Array_Indices,
                                       Cnt_Value.Array_Others,
                                       First_Index (AST_Type),
                                       Element_Type);
               end;
         end case;
      end Refine_Aux;

      ------------------
      -- Refine_Array --
      ------------------

      function Refine_Array
        (Arr_Indices  : Cntexmp_Value_Array.Map;
         Arr_Others   : Cntexmp_Value_Ptr;
         Arr_Indice   : Entity_Id;
         Element_Type : Entity_Id)
         return Unbounded_String
      is
         Indice_Type  : constant Entity_Id := Retysp (Etype (Arr_Indice));

         S   : Unbounded_String;
         Fst : Uint;
         Lst : Uint;
      begin
         Find_First_Static_Range (Arr_Indice, Fst, Lst);
         Append (S, "(");
         for C in Arr_Indices.Iterate loop
            declare
               Indice       : String renames Cntexmp_Value_Array.Key (C);
               Elem         : Cntexmp_Value_Ptr renames Arr_Indices (C);

               Ind_Val      : constant Cntexmp_Value_Ptr :=
                 new Cntexmp_Value'(T => Cnt_Integer,
                                    I => To_Unbounded_String (Indice));
               Ind_Printed  : constant Unbounded_String :=
                 Refine_Value (Ind_Val, Indice_Type, True);
               Elem_Printed : constant Unbounded_String :=
                 Refine_Value (Elem, Element_Type);
               Ind_Value    : constant Uint := UI_From_String (Indice);
            begin

               --  The other case happen when the index has an enumeration type
               --  and the value for this index given by cvc4 is outside of the
               --  range of the enumeration type.

               if Ind_Printed /= Null_Unbounded_String
                 and then UI_Le (Fst, Ind_Value)
                 and then UI_Le (Ind_Value, Lst)
               then
                  Append (S, Ind_Printed & " => " & Elem_Printed & ", ");
               end if;
            end;
         end loop;

         Append (S,
                 "others => " & Refine_Value (Arr_Others, Element_Type) & ")");

         return S;
      end Refine_Array;

      ------------------
      -- Refine_Value --
      ------------------

      function Refine_Value
        (Cnt_Value : Cntexmp_Value_Ptr;
         AST_Type  : Entity_Id;
         Is_Index  : Boolean := False)
         return Unbounded_String
      is
         Res : constant Unbounded_String :=
                 Refine_Aux (Cnt_Value, AST_Type, Is_Index);
      begin
         return Trim (Res, Both);
      end Refine_Value;

      -----------------
      -- Print_Float --
      -----------------

      function Print_Float (Cnt_Value : Cntexmp_Value)
                            return Unbounded_String
      is
         F : Float_Value renames Cnt_Value.F.all;
      begin
         case F.F_Type is
         when Float_Plus_Infinity | Float_Minus_Infinity | Float_NaN =>

            --  Decision: we don't print infinities or Nan
            return Null_Unbounded_String;

         when Float_Plus_Zero | Float_Minus_Zero =>

            --  Decision: we print zero+ and zero- as 0 (0.0 for type)
            return To_Unbounded_String ("0.0");

         when Float_Val =>
            declare
               F_S   : constant String := To_String (F.F_Sign);
               F_Si  : constant String := To_String (F.F_Significand);
               F_Exp : constant String := To_String (F.F_Exponent);
            begin
               return
                 To_Unbounded_String
                   (Ce_Pretty_Printing.StringBits_To_Approx
                      (F_S, F_Si, F_Exp));
            end;
         end case;
      end Print_Float;

      ---------------------------
      -- Replace_Question_Mark --
      ---------------------------

      function Replace_Question_Mark (S : Unbounded_String)
                                      return Unbounded_String
      is
      begin
         if S = "" then
            return To_Unbounded_String ("?");
         else
            return S;
         end if;
      end Replace_Question_Mark;

   --  Start of processing for Refine

   begin
      if Compile_Time_Known_And_Constant (AST_Node) then
         return Null_Unbounded_String;
      else
         return Refine_Value (Cnt_Value, Retysp (Etype (AST_Node)));
      end if;
   end Refine;

   ---------------------------
   -- Refine_Iterator_Value --
   ---------------------------

   function Refine_Iterator_Value
     (Cnt_Value : Cntexmp_Value_Ptr;
      Quant_Var : Entity_Id) return Unbounded_String
   is
      function Refine_Container_Iterator_Value
        (Cnt_Value      : Cntexmp_Value_Ptr;
         Cont_Typ       : Entity_Id;
         Container_Name : String) return Unbounded_String;
      --  Refine value for iterator over types with the Iterable aspect. For
      --  example, for a type:
      --
      --     type T is private
      --       Iterable => (First       => My_First,
      --                    Has_Element => My_Has_Element,
      --                    Next        => My_Next,
      --                    Element     => My_Element);
      --
      --  It will refine Cnt_Value to T's cursor type giving a value <value>
      --  and will return My_Element (Container_Name, <value>).
      --  If the type has an Iterable_For_Prrof of a model kind, it will be
      --  taken into account, for example, if we add:
      --
      --     type T2 is private
      --       Iterable => (First       => My_First_2,
      --                    Has_Element => My_Has_Element_2,
      --                    Next        => My_Next_2,
      --                    Element     => My_Element_2);
      --
      --     function Model (X : T) return T2;
      --     pragma Annotate (GNATprove, Iterable_For_Proof, "Model", Model);
      --
      --  then for of iterators on T will refined against T2's cursor type and
      --  then printed as My_Element_2 (Model (Container_Name), <value>).

      -------------------------------------
      -- Refine_Container_Iterator_Value --
      -------------------------------------

      function Refine_Container_Iterator_Value
        (Cnt_Value      : Cntexmp_Value_Ptr;
         Cont_Typ       : Entity_Id;
         Container_Name : String) return Unbounded_String
      is
         Found         : Boolean;
         Iterable_Info : Iterable_Annotation;

      begin
         --  Iteration is done on the cursor type of the ultimate model for
         --  proof. Go through Iterable_For_Proof annotations to find this
         --  type. Along the way, construct the expression to be used for the
         --  container name.

         Retrieve_Iterable_Annotation (Cont_Typ, Found, Iterable_Info);

         if Found then

            --  Iterable annotation should be a Model annotation. Indeed, if a
            --  Contains iterable annotation is provided, no temporary
            --  should be introduced for "for of" quantification.

            pragma Assert (Iterable_Info.Kind = SPARK_Annotate.Model);

            --  Prepend the name of the Model function to the container name
            --  and refine value on model type.

            return Refine_Container_Iterator_Value
              (Cnt_Value,
               Etype (Iterable_Info.Entity),
               Source_Name (Iterable_Info.Entity)
               & " (" & Container_Name & ")");
         else

            --  We have found the ultimate model type. Quantification is done
            --  on its cursor type.

            return Source_Name
              (Get_Iterable_Type_Primitive (Cont_Typ, Name_Element))
              & " (" & Container_Name & ", "
              & Refine (Cnt_Value,
                        Get_Cursor_Type (Cont_Typ))
              & ")";
         end if;
      end Refine_Container_Iterator_Value;

      function Is_Quantified_Expr (N : Node_Id) return Boolean is
        (Nkind (N) = N_Quantified_Expression);
      function Enclosing_Quantified_Expr is new
        First_Parent_With_Property (Is_Quantified_Expr);

      Container : constant Entity_Id :=
        Get_Container_In_Iterator_Specification
          (Iterator_Specification
             (Enclosing_Quantified_Expr (Quant_Var)));

      pragma Assert (Present (Container));

      Container_Name : constant String := Source_Name (Container);
      Typ            : constant Entity_Id := Retysp (Etype (Container));
   begin
      --  For arrays, quantification is done on the index type

      if Is_Array_Type (Typ) then
         return Container_Name & " ("
           & Refine (Cnt_Value, Etype (First_Index (Typ)))
           & ")";
      else
         return Refine_Container_Iterator_Value
           (Cnt_Value, Typ, Container_Name);
      end if;
   end Refine_Iterator_Value;

   ----------------------
   -- Refine_Attribute --
   ----------------------

   function Refine_Attribute (Cnt_Value : Cntexmp_Value_Ptr)
                              return Unbounded_String
   is
      Why3_Type : constant Cntexmp_Type := Cnt_Value.all.T;
   begin
      case Why3_Type is
         when Cnt_Integer =>
            return Cnt_Value.I;

         when Cnt_Bitvector =>
            return Cnt_Value.B;

         when Cnt_Unparsed =>
            return Cnt_Value.U;

         when others =>
            return Null_Unbounded_String;
      end case;

   end Refine_Attribute;

   -----------------------
   -- Build_Pretty_Line --
   -----------------------

   procedure Build_Pretty_Line
     (Variables               : Variables_Info;
      Pretty_Line_Cntexmp_Arr : out Cntexample_Elt_Lists.List)
   is
      use CNT_Elements;

      --  This record contain the name of the entity and the value of the
      --  corresponding counterexample generated by Why3 (used for attributes).
      type Name_And_Value is record
         Name  : Unbounded_String;
         Value : Unbounded_String;
      end record;

      package Names_And_Values is
        new Ada.Containers.Doubly_Linked_Lists
          (Element_Type => Name_And_Value);

      function Get_CNT_Element_Value
        (CNT_Element : CNT_Element_Ptr;
         Prefix      : Unbounded_String)
         return Unbounded_String;

      procedure Get_CNT_Element_Attributes
        (CNT_Element : CNT_Element_Ptr;
         Prefix      : Unbounded_String;
         Attributes  : in out Names_And_Values.List);
      --  Gets the attribute of an element and the attributes of its subfields

      function Get_CNT_Element_Value_And_Attributes
        (CNT_Element : CNT_Element_Ptr;
         Prefix      : Unbounded_String;
         Attributes  : in out Names_And_Values.List)
         return Unbounded_String;
      --  Gets the string value of given variable, record field or Attribute.
      --  If the value is of record type, the returned value is a record
      --  aggregate.
      --  If the value should not be displayed in countereexample, value
      --  "@not_display" is returned.
      --  In addition, recursively populate the list of attributes "Attributes"
      --  of CNT_Element and its fields if any attribute is found.

      --------------------------------
      -- Get_CNT_Element_Attributes --
      --------------------------------

      procedure Get_CNT_Element_Attributes
        (CNT_Element : CNT_Element_Ptr;
         Prefix      : Unbounded_String;
         Attributes  : in out Names_And_Values.List)
      is
         procedure Get_Attribute_Of_Component
           (Comp : Node_Id; Val : CNT_Element_Ptr);
         --  Get the attributes of record component or discriminant

         ---------------------------------
         --  Get_Attribute_Of_Component --
         ---------------------------------

         procedure Get_Attribute_Of_Component
           (Comp : Node_Id; Val : CNT_Element_Ptr)
         is
            Comp_Name  : constant String := Source_Name (Comp);
         begin
            Get_CNT_Element_Attributes
              (Val,
               Prefix & "." & Comp_Name,
               Attributes);
         end Get_Attribute_Of_Component;

         Element_Type : constant Entity_Id :=
           (if Present (CNT_Element.Entity) then
              Retysp
                (if Is_Class_Wide_Type (Etype (CNT_Element.Entity)) then
                    Get_Specific_Type_From_Classwide
                     (Etype (CNT_Element.Entity))
                 else Etype (CNT_Element.Entity))
            else
              Empty);

      begin

         for Att in CNT_Element.Attributes.Iterate loop

            --  Index is not a true Ada attribute, but a placeholder to
            --  represent the reference to the index (or cursor) associated to
            --  the quantified element type in a for of quantified expression.
            --  We print it E = A (<value>) or E = Element (C, <value>).

            if CNT_Attributes.Key (Att) = "Index" then
               declare
                  Refined_Value : constant Unbounded_String :=
                    Refine_Iterator_Value
                      (CNT_Attributes.Element (Att).Value,
                       CNT_Element.Entity);

               begin
                  Attributes.Append
                    (New_Item =>
                       (Name  => Prefix,
                        Value => Refined_Value));
               end;
            else
               declare
                  New_Prefix : constant Unbounded_String :=
                    Prefix & "'" & CNT_Attributes.Key (Att);

                  Attribute_Element : constant CNT_Element_Ptr :=
                    CNT_Attributes.Element (Att);
                  Refined_Value     : Unbounded_String;

               begin
                  --  Currently attributes are always printed as integers

                  if CNT_Attributes.Key (Att) in "First" | "Last" then
                     Refined_Value :=
                       Refine_Attribute (Attribute_Element.Value);
                  elsif CNT_Attributes.Key (Att) in "Result" | "Old" then
                     Refined_Value :=
                       Get_CNT_Element_Value_And_Attributes
                         (Attribute_Element,
                          Prefix,
                          Attributes);
                  else
                     Refined_Value :=
                       Refine_Attribute (Attribute_Element.Value);
                  end if;

                  --  Detecting the absence of value
                  if Refined_Value /= ""
                    and then Refined_Value /= "!"
                    and then Refined_Value /= "( )"
                    and then Refined_Value /= "()"
                  then
                     Attributes.Append
                       (New_Item =>
                          (Name  => New_Prefix,
                           Value => Refined_Value));
                  end if;
               end;
            end if;
         end loop;

         --  Following types should be ignored when exploring fields of
         --  CNT_Element.

         if No (Element_Type)
           or else not Is_Record_Type_In_Why (Element_Type)
         then
            return;
         end if;

         --  Check the attributes of the components

         for C in CNT_Element.Fields.Iterate loop
            if Is_Visible_In_Type (Element_Type, Key (C)) then
               Get_Attribute_Of_Component (Key (C), Element (C));
            end if;
         end loop;
      end Get_CNT_Element_Attributes;

      ---------------------------
      -- Get_CNT_Element_Value --
      ---------------------------

      function Get_CNT_Element_Value
        (CNT_Element : CNT_Element_Ptr;
         Prefix      : Unbounded_String)
         return Unbounded_String
      is
         Element_Type : constant Entity_Id :=
           (if Present (CNT_Element.Entity) then
              Retysp
                (if Is_Class_Wide_Type (Etype (CNT_Element.Entity)) then
                    Get_Specific_Type_From_Classwide
                     (Etype (CNT_Element.Entity))
                 else Etype (CNT_Element.Entity))
            else
              Empty);

      begin
         --  If Element_Type is not a "record" (anything with components or
         --  discriminants), return the value of the node.

         if not Is_Record_Type_In_Why (Element_Type) then
            declare
               Refined_Value : constant Unbounded_String :=
                 Refine (CNT_Element.Value,
                         CNT_Element.Entity);
            begin
               if Refined_Value = "" then
                  return Dont_Display;
               else
                  CNT_Element.Val_Str := Refined_Value;
                  return CNT_Element.Val_Str;
               end if;
            end;
         end if;

         --  If no field of the record is set and this is a record then we
         --  should have a record value associated to this element.

         if CNT_Element.Fields.Is_Empty then
            declare
               Refined_Value : constant Unbounded_String :=
                 Refine (CNT_Element.Value,
                         CNT_Element.Entity);
            begin
               if Refined_Value = "" then
                  return Dont_Display;
               else
                  CNT_Element.Val_Str := Refined_Value;
                  return (CNT_Element.Val_Str);
               end if;
            end;
         end if;

         declare
            Refined_Value : constant Unbounded_String :=
              Refine (CNT_Element.Value,
                      CNT_Element.Entity);
         begin
            --  Detecting the absence of value

            if Refined_Value /= ""
              and then Refined_Value /= "!"
              and then Refined_Value /= "( )"
              and then Refined_Value /= "()"
            then
               CNT_Element.Val_Str := Refined_Value;
               return CNT_Element.Val_Str;
            else
               --  No value were found for the variable so we need to recover
               --  the record field by field. We will go through all fields of
               --  CNT_Element and iterate on CNT_Element_Type components to
               --  get them in the right order.

               declare
                  Visibility_Map           : Component_Visibility_Maps.Map :=
                    Get_Component_Visibility_Map (Element_Type);

                  Fields_Discrs_With_Value : Natural := 0;
                  --  Not using the base_type here seems ok since
                  --  counterexamples should be projected in this part of
                  --  the code

                  Ordered_Values : Ordered_Sloc_Map.Map;
                  --  Ordered map containing the values for the components of
                  --  the record. They are ordered in as in the source file,
                  --  inherited components coming first.

                  procedure Get_Value_Of_Component
                    (Comp       : Node_Id;
                     Val        : Unbounded_String;
                     Visibility : Component_Visibility);
                  --  Insert value of record component or dicriminant in
                  --  Ordered_Values.

                  ----------------------------
                  -- Get_Value_Of_Component --
                  ----------------------------

                  procedure Get_Value_Of_Component
                    (Comp       : Node_Id;
                     Val        : Unbounded_String;
                     Visibility : Component_Visibility)
                  is
                     Comp_Name : constant String :=
                       Source_Name (Comp);
                     Orig_Comp : constant Entity_Id :=
                       Search_Component_In_Type
                         (Original_Declaration (Comp), Comp);
                     Expl      : constant String :=
                       (if Ekind (Comp) /= E_Discriminant
                        and then Visibility = Duplicated
                        then
                           " <hidden" &
                        (if Sloc (Orig_Comp) > 0 then
                              ", defined at "
                           & Build_Location_String
                             (Sloc (Orig_Comp))
                           else "") & ">"
                        else "");
                     --  Explanation. It is empty except for duplicated
                     --  components where it points to the declaration of the
                     --  component.

                  begin
                     Ordered_Values.Insert
                       (Get_Loc_Info (Comp),
                        Comp_Name & " => " & Val & Expl);
                     Fields_Discrs_With_Value :=
                       Fields_Discrs_With_Value + 1;
                  end Get_Value_Of_Component;

               begin
                  --  Add discriminants to Visibility_Map. Discriminants are
                  --  considered to be always visible.

                  if Has_Discriminants (Element_Type) then
                     declare
                        Discr : Entity_Id :=
                          First_Discriminant (Element_Type);
                     begin
                        while Present (Discr) loop
                           Visibility_Map.Insert
                             (Root_Record_Component (Discr), Regular);
                           Next_Discriminant (Discr);
                        end loop;
                     end;
                  end if;

                  --  Go over counterexample values for record fields to fill
                  --  the Ordered_Values map. Along the way, remove seen
                  --  components from the Visibility_Map so that we can later
                  --  check for unseen components.

                  for C in CNT_Element.Fields.Iterate loop
                     declare
                        Comp       : Entity_Id renames Key (C);
                        Comp_Name  : constant String :=
                          Source_Name (Comp);
                        Comp_Val   : constant Unbounded_String :=
                          Get_CNT_Element_Value
                            (Element (C),
                             Prefix & "." & Comp_Name);
                        Visibility : Component_Visibility;

                     begin
                        if Comp_Val /= Dont_Display then
                           if not Is_Type (Comp) then
                              declare
                                 Orig_Comp : constant Entity_Id :=
                                   Search_Component_In_Type
                                     (Element_Type, Comp);
                              begin
                                 Visibility := Visibility_Map (Orig_Comp);
                                 Visibility_Map.Exclude (Orig_Comp);
                              end;

                           --  Type component are not displayed as they stand
                           --  for invisible components.

                           else
                              Visibility := Removed;
                           end if;

                           if Visibility /= Removed then
                              pragma Assert (Comp_Val /= "?");
                              Get_Value_Of_Component
                                (Comp, Comp_Val, Visibility);
                           end if;
                        end if;
                     end;
                  end loop;

                  --  If there are no fields and discriminants of the processed
                  --  value with values that can be displayed, do not display
                  --  the value (this can happen if there were collected
                  --  fields or discrinants, but their values should not
                  --  be displayed).

                  if Fields_Discrs_With_Value = 0 then
                     return Dont_Display;
                  end if;

                  --  Go over the visibility map to see if they are missing
                  --  components.

                  declare
                     Is_Before    : Boolean := False;
                     Need_Others  : Boolean := False;
                     --  True if there are more than one missing value or if
                     --  the record contains invisble fields (component of type
                     --  kind).

                     First_Unseen : Entity_Id := Empty;
                     --  First component for which we are missing a value

                     Value        : Unbounded_String :=
                       To_Unbounded_String ("(");
                  begin
                     for C in Visibility_Map.Iterate loop
                        declare
                           Visibility : Component_Visibility renames
                             Component_Visibility_Maps.Element (C);
                           Comp       : Entity_Id renames
                             Component_Visibility_Maps.Key (C);
                        begin
                           if Visibility /= Removed then
                              if Is_Type (Comp) or else Present (First_Unseen)
                              then
                                 Need_Others := True;
                                 exit;
                              else
                                 First_Unseen := Comp;
                              end if;
                           end if;
                        end;
                     end loop;

                     --  If there is only one component which does not have a
                     --  value, we output directly a ? for its value instead
                     --  of introducing a others case.

                     if not Need_Others and then Present (First_Unseen) then
                        Get_Value_Of_Component
                          (First_Unseen, To_Unbounded_String ("?"),
                           Visibility_Map.Element (First_Unseen));
                     end if;

                     --  Construct the counterexample value by appending the
                     --  components in the right order.

                     for V of Ordered_Values loop
                        Append (Value,
                                (if Is_Before then ", " else "") & V);
                        Is_Before := True;
                     end loop;

                     --  If there are more than one fields that are not
                     --  mentioned in the counterexample, summarize them using
                     --  the field others.

                     if Need_Others then
                        Append (Value,
                                (if Is_Before then ", " else "") &
                                  "others => ?");
                     end if;
                     Append (Value, ")");

                     return Value;
                  end;
               end;
            end if;
         end;
      end Get_CNT_Element_Value;

      ------------------------------------------
      -- Get_CNT_Element_Value_And_Attributes --
      ------------------------------------------

      function Get_CNT_Element_Value_And_Attributes
        (CNT_Element : CNT_Element_Ptr;
         Prefix      : Unbounded_String;
         Attributes  : in out Names_And_Values.List)
         return Unbounded_String
      is
      begin
         --  Fill in first the values of attributes so that we can ignore
         --  attributes in what follows.
         Get_CNT_Element_Attributes (CNT_Element,
                                     Prefix,
                                     Attributes);

         --  Return the value
         return Get_CNT_Element_Value (CNT_Element, Prefix);
      end Get_CNT_Element_Value_And_Attributes;

   --  Start of processing for Build_Pretty_Line

   begin
      Pretty_Line_Cntexmp_Arr := Cntexample_Elt_Lists.Empty_List;

      for Var of Variables.Variables_Order loop
         declare
            Variable : Cursor :=
              Variables.Variables_Map.Find (Var.Id);
            Var_Name : constant Unbounded_String := Var.Name;

            Attributes : Names_And_Values.List;

         begin
            if Has_Element (Variable) then
               declare

                  Var_Value : constant Unbounded_String :=
                                Get_CNT_Element_Value_And_Attributes
                                  (Element (Variable),
                                   Var_Name,
                                   Attributes);

                  procedure Add_CNT (Name, Value : Unbounded_String);
                  --  Append a cnt variable and its value to the list

                  -------------
                  -- Add_CNT --
                  -------------

                  procedure Add_CNT (Name, Value : Unbounded_String) is
                  begin
                     --  If the value of the variable should not be displayed
                     --  in the counterexample, do not display the variable.

                     if Value /= Dont_Display then
                        Pretty_Line_Cntexmp_Arr.Append
                          (Cntexample_Elt'(Kind    => CEE_Variable,
                                           Name    => Name,
                                           --  Labels not necessary at this
                                           --  point
                                           Labels  => S_String_List.Empty_List,
                                           Value   => Element (Variable).Value,
                                           Val_Str => Value));
                     end if;
                  end Add_CNT;

               begin
                  Add_CNT (Var_Name, Var_Value);

                  for Att of Attributes loop
                     Add_CNT (Att.Name, Att.Value);
                  end loop;

                  Next (Variable);
               end;
            end if;
         end;
      end loop;
   end Build_Pretty_Line;

   --------------------------
   -- Build_Variables_Info --
   --------------------------

   procedure Build_Variables_Info
     (File             : String;
      Line             : Natural;
      Line_Cntexmp_Arr : Cntexample_Elt_Lists.List;
      Variables        : in out Variables_Info)
   is
      function Insert_CNT_Element
        (Entity : Entity_Id;
         Map    : CNT_Element_Map_Ptr)
         return CNT_Element_Ptr;
      --  Insert a CNT_Element with given entity to the given map. If
      --  it has already been inserted, return the existing; if not, create new
      --  entry, store it in the map, and return it.

      function Insert_CNT_Element
        (Name   : String;
         Entity : Entity_Id;
         Map    : CNT_Attributes_Map_Ptr)
         return CNT_Element_Ptr;
      --  Insert a CNT_Element with given name and entity to the given map. If
      --  it has already been inserted, return the existing; if not, create new
      --  entry, store it in the map, and return it.

      ------------------------
      -- Insert_CNT_Element --
      ------------------------

      function Insert_CNT_Element
        (Name   : String;
         Entity : Entity_Id;
         Map    : CNT_Attributes_Map_Ptr)
         return CNT_Element_Ptr
      is
         use CNT_Attributes;
         Var : CNT_Element_Ptr;

      begin
         if Map.Contains (Name) then
            Var := Map.Element (Name);
         else
            Var := new CNT_Element'
              (Entity     => Entity,
               Attributes => new CNT_Attributes.Map,
               Fields     => new CNT_Elements.Map,
               Value      => new Cntexmp_Value'
                 (T => Cnt_Invalid,
                  S => Null_Unbounded_String),
               Val_Str    => Null_Unbounded_String);

            Include (Container => Map.all,
                     Key       => Name,
                     New_Item  => Var);
         end if;

         return Var;
      end Insert_CNT_Element;

      ------------------------
      -- Insert_CNT_Element --
      ------------------------

      function Insert_CNT_Element
        (Entity : Entity_Id;
         Map    : CNT_Element_Map_Ptr)
         return CNT_Element_Ptr
      is
         use CNT_Elements;
         Var : CNT_Element_Ptr;

      begin
         if Map.Contains (Entity) then
            Var := Map.Element (Entity);
         else
            Var := new CNT_Element'
              (Entity     => Entity,
               Attributes => new CNT_Attributes.Map,
               Fields     => new CNT_Elements.Map,
               Value      => new Cntexmp_Value'
                 (T => Cnt_Invalid,
                  S => Null_Unbounded_String),
               Val_Str    => Null_Unbounded_String);

            Include (Container => Map.all,
                     Key       => Entity,
                     New_Item  => Var);
         end if;

         return Var;
      end Insert_CNT_Element;

   --  Start of processing for Build_Variables_Info

   begin
      for Elt of Line_Cntexmp_Arr loop

         declare
            Name_Parts : String_Split.Slice_Set;
            Current_Subfields_Map : CNT_Element_Map_Ptr :=
              Variables.Variables_Map'Unchecked_Access;
            Current_Attributes_Map : CNT_Attributes_Map_Ptr :=
              new CNT_Attributes.Map;
         begin

            --  There is either one model element with its name corresponding
            --  to an error message. No variable map is built in this case.

            if Elt.Kind = CEE_Error_Msg then
               return;
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
            --  Attribute ::= | Attr_type
            --                | Attr_type " (" num ")"
            --  Attr_type ::= | "First"
            --                | "Last"
            --                | "attr__constrained"
            --                | "attr__tag"
            --
            --  num := [0-9]+
            --
            --  See Bound_Dimension_To_Str for more information on the "(5)"
            --  notation.
            --  See Attr_To_Why_Name for Attr_type cases and To_string on
            --  Why_Name_Enum type
            --
            --  The ENTITY_ID in first Part corresponds to a
            --  variable, others to record fields.

            --  Split Name into sequence of Part
            String_Split.Create (S          => Name_Parts,
                                 From       => To_String (Elt.Name),
                                 Separators => ".'",
                                 Mode       => String_Split.Single);

            --  For every Part, we create a CNT_Element
            for Var_Slice_Num in 1 .. String_Split.Slice_Count (Name_Parts)
            loop
               declare

                  function Try_Get_Part_Entity (Part : String)
                                                return Entity_Id;
                  --  Try to cast Part into an Entity_Id, return empty id if it
                  --  doesn't work.

                  -------------------------
                  -- Try_Get_Part_Entity --
                  -------------------------

                  function Try_Get_Part_Entity (Part : String)
                                                return Entity_Id
                  is
                  begin
                     return Entity_Id'Value (Part);
                  exception
                     when Constraint_Error =>
                        return Empty;
                  end Try_Get_Part_Entity;

                  Part : constant String := Slice (Name_Parts, Var_Slice_Num);

                  Part_Entity : constant Entity_Id :=
                    Try_Get_Part_Entity (Part);
                  --  Note that if Var_Slice_Num = 1, Part_Entity is Entity_Id
                  --  of either declaration of argument of a function
                  --  or declaration of a variable (corresponding to the
                  --  counterexample element being processed) If Var_Slice_Num
                  --  > 1, Part_Entity is Entity_Id of declaration of record
                  --  field or discriminant.

                  Is_Attribute : Boolean := No (Part_Entity);

                  --  If Part does not cast into an entity_id it is treated as
                  --  an attribute.

                  Part_Name : Unbounded_String :=
                    To_Unbounded_String
                      (if Is_Attribute
                       then Part
                       else Source_Name (Part_Entity));
                  Current_CNT_Element : CNT_Element_Ptr;

               begin
                  if Var_Slice_Num = 1 then

                     --  Process the first Entity_Id, which corresponds to a
                     --  variable.

                     --  Do not display uninitialized counterexample elements
                     --  (elements corresponding to uninitialized variables or
                     --  function arguments).

                     if Present (Part_Entity)
                       and then Is_Uninitialized (Part_Entity, File, Line)
                     then
                        goto Next_Model_Element;
                     end if;

                     --  Store variable to Variable_List

                     if not Variables.Variables_Order.Contains
                       ((Id => Part_Entity, Name => Part_Name))
                     then
                        Variables.Variables_Order.Include
                          ((Id => Part_Entity, Name => Part_Name));
                     end if;

                     --  Possibly Append attributes 'Old or
                     --  'Result after its name

                     if (Elt.Kind = CEE_Old
                         and then Nkind (Part_Entity) in N_Entity
                         and then Ekind (Part_Entity) in
                           E_In_Out_Parameter | E_Out_Parameter)
                       or else Elt.Kind = CEE_Result
                     then
                        Current_CNT_Element := Insert_CNT_Element
                          (Entity => Part_Entity,
                           Map    => Current_Subfields_Map);

                        Current_Subfields_Map :=
                          Current_CNT_Element.Fields;
                        Current_Attributes_Map :=
                          Current_CNT_Element.Attributes;

                        Part_Name := To_Unbounded_String
                          (if Elt.Kind = CEE_Old
                           then "Old"
                           else "Result");
                        Is_Attribute := True;

                     end if;
                  end if;

                  Current_CNT_Element :=
                    (if Is_Attribute then
                        Insert_CNT_Element
                       (Name   => To_String (Part_Name),
                        Entity => Part_Entity,
                        Map    => Current_Attributes_Map)
                     else Insert_CNT_Element
                       (Entity => Part_Entity,
                        Map    => Current_Subfields_Map));

                  --  Note that Value is set even if it has already been
                  --  set. Overriding of value happens if a loop is unrolled
                  --  (see Gnat2Why.Expr.Loops.Wrap_Loop) and the VC for
                  --  that the counterexample was generated is for a loop
                  --  iteration. In this case, there are both counterexample
                  --  elements for variables in an unrolling of the loop
                  --  and a loop iteration and these counterexample elements
                  --  have the same names and locations (but can have
                  --  different values). Note that in this case only the
                  --  counterexample elements for the loop iteration are
                  --  relevant for the proof. Counterexample elements
                  --  are reported in the order in that the corresponding
                  --  variables are in generated why code and thus using the
                  --  last counterexample element with given Name ensures
                  --  the correct behavior.

                  if Var_Slice_Num = Slice_Count (Name_Parts) then
                     Current_CNT_Element.Value := new
                       Cntexmp_Value'(Elt.Value.all);
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

   ---------------------------
   -- Create_Pretty_Cntexmp --
   ---------------------------

   function Create_Pretty_Cntexmp
     (Cntexmp : Cntexample_File_Maps.Map;
      VC_Loc  : Source_Ptr)
      return Cntexample_File_Maps.Map
   is
      procedure Create_Pretty_Line
        (Pretty_File_Cntexmp : in out Cntexample_Lines;
         File                : String;
         Line                : Natural;
         Line_Cntexmp        : Cntexample_Elt_Lists.List);
      --  Pretty prints counterexample model elements at a single source
      --  code location (line).

      ------------------------
      -- Create_Pretty_Line --
      ------------------------

      procedure Create_Pretty_Line
        (Pretty_File_Cntexmp : in out Cntexample_Lines;
         File                : String;
         Line                : Natural;
         Line_Cntexmp        : Cntexample_Elt_Lists.List)
      is
         use CNT_Elements;

         Variables : Variables_Info;
         Pretty_Line_Cntexmp_Arr : Cntexample_Elt_Lists.List;

      --  Start of processing for Create_Pretty_Line

      begin
         Build_Variables_Info (File, Line, Line_Cntexmp, Variables);

         if not Is_Empty (Variables.Variables_Map) then
            Build_Pretty_Line (Variables, Pretty_Line_Cntexmp_Arr);

            --  Add the counterexample line only if there are some
            --  pretty printed counterexample elements
            if not Pretty_Line_Cntexmp_Arr.Is_Empty then
               Pretty_File_Cntexmp.Other_Lines.Insert
                 (Line, Pretty_Line_Cntexmp_Arr);
            end if;
         end if;
      end Create_Pretty_Line;

      File : constant String := File_Name (VC_Loc);
      Line : constant Logical_Line_Number :=
        Get_Logical_Line_Number (VC_Loc);
      Remapped_Cntexmp : constant Cntexample_File_Maps.Map :=
        Remove_Irrelevant_Branches
          (Remap_VC_Info (Cntexmp, File, Natural (Line)));
      Pretty_Cntexmp : Cntexample_File_Maps.Map :=
        Cntexample_File_Maps.Empty_Map;

      use Cntexample_File_Maps;

   --  Start of processing for Create_Pretty_Cntexmp

   begin
      for File_C in Remapped_Cntexmp.Iterate loop
         declare
            Pretty_File_Cntexmp : Cntexample_Lines :=
             Cntexample_Lines'(VC_Line     =>
                                 Cntexample_Elt_Lists.Empty_List,
                               Other_Lines =>
                                 Cntexample_Line_Maps.Empty_Map);

            Filename  : String renames Key (File_C);
            Lines_Map : Cntexample_Line_Maps.Map renames
              Element (File_C).Other_Lines;

         begin
            for Line_C in Lines_Map.Iterate loop
               Create_Pretty_Line
                 (Pretty_File_Cntexmp,
                  Filename,
                  Cntexample_Line_Maps.Key (Line_C),
                  Lines_Map (Line_C));
            end loop;

            --  At this point, the information of VC_line is now in the
            --  Other_Lines field because Remap_VC_Info was applied.
            if Is_Ada_File_Name (Filename) and then
              not Cntexample_Line_Maps.Is_Empty
                (Pretty_File_Cntexmp.Other_Lines)
            then
               Pretty_Cntexmp.Insert (Filename, Pretty_File_Cntexmp);
            end if;
         end;
      end loop;

      return Pretty_Cntexmp;
   end Create_Pretty_Cntexmp;

   ---------------------------
   -- Get_Cntexmp_One_Liner --
   ---------------------------

   function Get_Cntexmp_One_Liner
     (Cntexmp : Cntexample_File_Maps.Map;
      VC_Loc  : Source_Ptr)
      return String
   is
      function Get_Cntexmp_Line_Str
        (Cntexmp_Line : Cntexample_Elt_Lists.List) return String;

      --------------------------
      -- Get_Cntexmp_Line_Str --
      --------------------------

      function Get_Cntexmp_Line_Str
        (Cntexmp_Line : Cntexample_Elt_Lists.List) return String
      is
         Cntexmp_Line_Str : Unbounded_String;

      begin
         for Elt of Cntexmp_Line loop
            if Cntexmp_Line_Str /= "" then
               Append (Cntexmp_Line_Str, " and ");
            end if;
            Append (Cntexmp_Line_Str, Elt.Name);
            if Elt.Kind /= CEE_Error_Msg then
               Append (Cntexmp_Line_Str, " = ");
               Append (Cntexmp_Line_Str, Elt.Val_Str);
            end if;
         end loop;
         return To_String (Cntexmp_Line_Str);
      end Get_Cntexmp_Line_Str;

      File : constant String := File_Name (VC_Loc);
      Line : constant Logical_Line_Number := Get_Logical_Line_Number (VC_Loc);
      File_Cur : constant Cntexample_File_Maps.Cursor := Cntexmp.Find (File);
      Cntexmp_Line : Cntexample_Elt_Lists.List :=
        Cntexample_Elt_Lists.Empty_List;

   --  Start of processing for Get_Cntexmp_One_Liner

   begin
      if Cntexample_File_Maps.Has_Element (File_Cur) then
         declare
            Line_Map : Cntexample_Line_Maps.Map renames
              Cntexmp (File_Cur).Other_Lines;
            Line_Cur : constant Cntexample_Line_Maps.Cursor :=
              Line_Map.Find (Natural (Line));
         begin
            if Cntexample_Line_Maps.Has_Element (Line_Cur) then
               Cntexmp_Line := Line_Map (Line_Cur);
            end if;
         end;
      end if;
      return Get_Cntexmp_Line_Str (Cntexmp_Line);
   end Get_Cntexmp_One_Liner;

   ----------------------
   -- Is_Ada_File_Name --
   ----------------------

   function Is_Ada_File_Name (File : String) return Boolean is
   begin
      return
        File'Length >= 4 and then
        (File ((File'Last - 2) .. File'Last) in "adb" | "ads");
   end Is_Ada_File_Name;

   ----------------------
   -- Is_Uninitialized --
   ----------------------

   function Is_Uninitialized
     (Element_Decl : Entity_Id;
      Element_File : String;
      Element_Line : Natural)
      return Boolean
   is
   begin
      --  Counterexample element can be uninitialized only if its location
      --  is the same as location of its declaration (otherwise it has been
      --  assigned or it is a part of construct that triggers VC - and flow
      --  analysis would issue an error in this case).

      if File_Name (Sloc (Element_Decl)) = Element_File
        and then
          Natural
            (Get_Logical_Line_Number (Sloc (Element_Decl))) = Element_Line
      then

         --  Uninitialized procedure parameter

         return Ekind (Element_Decl) = E_Out_Parameter

         --  Uninitialized variable

           or else (Ekind (Element_Decl) = E_Variable
                    and then Nkind (Enclosing_Declaration (Element_Decl)) =
                      N_Object_Declaration
                    and then
                    No (Expression (Enclosing_Declaration (Element_Decl)))
                    and then
                    Default_Initialization
                      (Etype (Element_Decl), Get_Flow_Scope (Element_Decl)) =
                        No_Default_Initialization);
      end if;

      return False;
   end Is_Uninitialized;

   -----------------------------
   -- Print_CNT_Element_Debug --
   -----------------------------

   function Print_CNT_Element_Debug (El : CNT_Element) return String is
      R : Unbounded_String := "[ " & El.Val_Str & " | ";
   begin
      for F in El.Fields.Iterate loop
         Append (R, "<F- " & Short_Name (CNT_Elements.Key (F)) &
                    " = " &
                    Print_CNT_Element_Debug (CNT_Elements.Element (F).all) &
                    " -F>");
      end loop;

      for F in El.Attributes.Iterate loop
         Append (R, "<A- " & CNT_Attributes.Key (F) &
                    " = " &
                    Print_CNT_Element_Debug (CNT_Attributes.Element (F).all) &
                    " -A>");
      end loop;

      return To_String (R & " ]");
   end Print_CNT_Element_Debug;

   --------------------------------
   -- Remove_Irrelevant_Branches --
   --------------------------------

   --  This is the main function of a feature which records a boolean
   --  counterexample value for any branching condition done in the code (if
   --  and case). These counterexamples are tagged with a specific attribute
   --  "branch_id:number" (with number being the node_id of the if/case).
   --  In this context, this function first search for the node_id labels of
   --  counterexamples and then removes the lines that do not corresponds to
   --  the branch taken by the counterexample in the if/case (using the value
   --  of the CE).

   function Remove_Irrelevant_Branches
     (Cntexmp : Cntexample_File_Maps.Map)
      return Cntexample_File_Maps.Map
   is

      package Supp_Lines is new Ce_Interval_Sets (N => Physical_Line_Number);

      function Get_Interval_Case (N : Node_Id;
                                  B : Boolean)
                                  return Supp_Lines.Interval_Set
        with Pre => Nkind (N) = N_Case_Statement_Alternative;
      --  The case statement are translated to new ifs in Why3 so we can
      --  eliminate case by case (the order of branches is kept):
      --  * a branch is taken: we can remove all the subsequent "when"
      --    statements (they are not taken). We *cannot* remove branches
      --    * before * this one as, if an earlier branch was taken the model
      --    is still correct if the current one is also taken (making it
      --    inconsistent).
      --  * a branch is not taken: we can remove it as we are sure it is not
      --    taken

      function Get_Interval_For_Branch (N : Node_Id)
                                        return Supp_Lines.Interval
        with Pre => Nkind (N) in N_If_Statement | N_Elsif_Part;

      function Get_Interval_For_Branch_Case (N : Node_Id)
                                             return Supp_Lines.Interval
        with Pre => Nkind (N) = N_Case_Statement_Alternative;

      function Get_Interval_If (N : Node_Id;
                                B : Boolean)
                                return Supp_Lines.Interval_Set
        with Pre => Nkind (N) in N_If_Statement | N_Elsif_Part;

      function Get_P (E : Entity_Id) return Physical_Line_Number is
        (Get_Physical_Line_Number (Sloc (E)));
      --  Abbreviation for querying the first line of an entity

      procedure Search_Labels (S : in out Supp_Lines.Interval_Set;
                               L : S_String_List.List;
                               V : Cntexmp_Value_Ptr);
      --  This procedure fills S with new values corresponding to branches that
      --  should not be taken for display of counterexamples.

      -----------------------
      -- Get_Interval_Case --
      -----------------------

      function Get_Interval_Case (N : Node_Id;
                                  B : Boolean)
                                  return Supp_Lines.Interval_Set
      is
         S : Supp_Lines.Interval_Set := Supp_Lines.Create;
      begin

         if not B then
            --  This branch is not taken, remove it

            Supp_Lines.Insert (S, Get_Interval_For_Branch_Case (N));
            return S;

         else
            --  This branch is taken, removes all branches *after* it. If one
            --  is taken before, the result is random because it is a part of
            --  a logic expression that is never used -> nothing more can be
            --  deduced.

            if Present (Next (N)) then
               Supp_Lines.Insert
                 (S, (L_Bound => Get_P (Next (N)),
                      R_Bound =>
                        Get_Physical_Line_Number (
                          End_Location (Enclosing_Statement (N)))));
            end if;

         end if;
         return S;
      end Get_Interval_Case;

      -----------------------------
      -- Get_Interval_For_Branch --
      -----------------------------

      function Get_Interval_For_Branch (N : Node_Id)
                                        return Supp_Lines.Interval
      is
      begin
         if Nkind (N) = N_If_Statement then

            return (L_Bound => Get_P (Nlists.First (Then_Statements (N))),
                    R_Bound =>

                      (if Present (Elsif_Parts (N)) then
                          Physical_Line_Number'Max
                            (1,
                             Get_P (First (Elsif_Parts (N))) - 1)
                       elsif Present (Else_Statements (N)) then
                          Physical_Line_Number'Max
                            (1,
                             Get_P (First (Else_Statements (N))) - 1)
                       else
                          Get_Physical_Line_Number (End_Location (N))));

         elsif Nkind (N) = N_Elsif_Part then

            return (L_Bound => Get_P (First (Then_Statements (N))),
                    R_Bound =>

                      (if Present (Next (N)) then
                          Physical_Line_Number'Max (1, Get_P (Next (N)) - 1)
                       else

                         --  There is an elsif statements so there is an else
                         --  statement

                         (if Present
                              (Else_Statements (Enclosing_Statement (N)))
                          then
                             Get_P (First
                            (Else_Statements (Enclosing_Statement (N))))
                          else
                             Get_Physical_Line_Number
                               (End_Location (Enclosing_Statement (N))))));
         else

            --  Cannot be accessed (precondition)
            raise Program_Error;
         end if;
      end Get_Interval_For_Branch;

      ----------------------------------
      -- Get_Interval_For_Branch_Case --
      ----------------------------------

      function Get_Interval_For_Branch_Case (N : Node_Id)
                                             return Supp_Lines.Interval
      is
      begin
         if Present (Next (N)) then
            return (L_Bound => Get_P (N),
                    R_Bound =>
                      Physical_Line_Number'Max (1, Get_P (Next (N)) - 1));
         else
            return (L_Bound => Get_P (N),
                    R_Bound =>
                      Physical_Line_Number
                        (End_Location (Enclosing_Statement (N))));
         end if;

      end Get_Interval_For_Branch_Case;

      ---------------------
      -- Get_Interval_If --
      ---------------------

      --  The elsif statement are translated to new ifs in Why3 so we can
      --  eliminate branch by branch (the order of branches is kept):
      --  * a branch is taken: we can remove all the subsequent elsif/else
      --    statements (they are not taken). We *cannot* remove branches
      --    * before * this one as, if an earlier branch was taken the model
      --    is still correct if the current one is also taken (making it
      --    inconsistent).
      --  * a branch is not taken: we can remove it as we are sure it is not
      --    taken

      function Get_Interval_If (N : Node_Id;
                                B : Boolean)
                                return Supp_Lines.Interval_Set
      is
         S : Supp_Lines.Interval_Set := Supp_Lines.Create;
      begin

         if not B then
            --  This branch is not taken: remove it.

            Supp_Lines.Insert (S, Get_Interval_For_Branch (N));
            return S;

         else
            --  This branch is taken, removes all branches *after* it. If one
            --  is taken before, the result is random because it is a part of
            --  a logic expression that is never used -> nothing more can be
            --  deduced.

            if Nkind (N) = N_If_Statement then
               if Present (Elsif_Parts (N)) then
                  Supp_Lines.Insert
                    (S, (L_Bound => Get_P (First (Elsif_Parts (N))),
                         R_Bound =>
                           Get_Physical_Line_Number (End_Location (N))));

               elsif Present (Else_Statements (N)) then
                  Supp_Lines.Insert
                    (S, (L_Bound => Get_P (First (Else_Statements (N))),
                         R_Bound =>
                           Get_Physical_Line_Number (End_Location (N))));
               else

                  --  No elsif or else branch so we don't need to remove
                  --  anything
                  null;
               end if;

            elsif Nkind (N) = N_Elsif_Part then

               if Present (Next (N)) then
                  Supp_Lines.Insert
                    (S, (L_Bound => Get_P (Next (N)),
                         R_Bound =>
                           Get_Physical_Line_Number (
                             End_Location (Enclosing_Statement (N)))));

               else

                  --  If there is no else statements and no following elsif we
                  --  do nothing.

                  if Present (Else_Statements (Enclosing_Statement (N))) then
                     Supp_Lines.Insert
                       (S, (L_Bound =>
                                Get_P (First
                                 (Else_Statements (Enclosing_Statement (N)))),
                            R_Bound =>
                              Get_Physical_Line_Number (
                                End_Location (Enclosing_Statement (N)))));
                  end if;
               end if;

            else
               raise Constraint_Error;
            end if;

            return S;
         end if;
      end Get_Interval_If;

      -------------------
      -- Search_Labels --
      -------------------

      procedure Search_Labels (S : in out Supp_Lines.Interval_Set;
                               L : S_String_List.List;
                               V : Cntexmp_Value_Ptr)
      is
      begin

         for Elt of L loop
            declare
               Str : constant String := To_String (Elt);
            begin

               if Str'Length > 10 and then
                 Str (Str'First .. Str'First + 9) = "branch_id:"
               then

                  declare
                     N : constant Node_Id := Get_Entity_Id
                       (False, Str (Str'First + 10 .. Str'Last));
                  begin
                     if Present (N) and V.T = Cnt_Boolean then

                        if Nkind (N) in N_If_Statement | N_Elsif_Part
                        then
                           Supp_Lines.Insert_Union
                             (S,
                              Get_Interval_If (N, V.Bo));

                        elsif Nkind (N) = N_Case_Statement_Alternative then
                           Supp_Lines.Insert_Union
                             (S,
                              Get_Interval_Case (N, V.Bo));

                        else
                           null;
                        end if;
                     end if;
                  end;
               end if;
            end;
         end loop;

      end Search_Labels;

      --  Start of processing for Remove_Irrelevant_Branches

      Remapped_Cntexmp : Cntexample_File_Maps.Map := Cntexmp;
      --  Temporary variable containing the branch to remove in files
      Suppressed_Lines : Supp_Lines.Interval_Set := Supp_Lines.Create;
   begin
      --  VC_Line is already empty at this point

      for Files of Remapped_Cntexmp loop
         Supp_Lines.Clear (Suppressed_Lines);

         --  Collect node_ids that remove lines in Suppressed_Lines
         for Lines of Files.Other_Lines loop
            for Elt of Lines loop
               Search_Labels (Suppressed_Lines, Elt.Labels, Elt.Value);
            end loop;
         end loop;

         declare
            Cnt_Line_Map : Cntexample_Line_Maps.Map :=
                             Cntexample_Line_Maps.Empty_Map;
         begin

            --  remove lines according to suppressed_lines collected
            for Cursor in Files.Other_Lines.Iterate loop
               declare
                  Line : constant Natural := Cntexample_Line_Maps.Key (Cursor);
               begin

                  if not Supp_Lines.Has_Containing_Interval
                    (Suppressed_Lines,
                     Physical_Line_Number (Line))
                  then
                     Cntexample_Line_Maps.Insert (Cnt_Line_Map, Line,
                                                  Cntexample_Line_Maps.Element
                                                    (Cursor));
                  end if;
               end;
            end loop;
            Files.Other_Lines := Cnt_Line_Map;
         end;
      end loop;

      return Remapped_Cntexmp;
   end Remove_Irrelevant_Branches;

   -------------------
   -- Remap_VC_Info --
   -------------------

   function Remap_VC_Info
     (Cntexmp : Cntexample_File_Maps.Map;
      VC_File : String;
      VC_Line : Natural)
      return Cntexample_File_Maps.Map
   is
      Remapped_Cntexmp : Cntexample_File_Maps.Map := Cntexmp;

      C        : Cntexample_File_Maps.Cursor;
      Inserted : Boolean;
      VC       : Cntexample_Elt_Lists.List;

   begin
      --  Search for VC_Line (there is only one). It can be in any file,
      --  depending on the location used by Why3 (when checking that a
      --  predicate holds, it sometimes uses the location of the predicate
      --  instead of the location where it is called).

      for Elt of Remapped_Cntexmp loop
         if not Elt.VC_Line.Is_Empty then
            pragma Assert (VC.Is_Empty);
            VC := Elt.VC_Line;
            Elt.VC_Line.Clear;
         end if;
      end loop;

      --  Insert it at the appropriate location in Remapped_Cntexmp, possibly
      --  deleting other information in the process.

      Remapped_Cntexmp.Insert
        (Key      => VC_File,
         New_Item => (Other_Lines => Cntexample_Line_Maps.Empty_Map,
                      VC_Line     => Cntexample_Elt_Lists.Empty_List),
         Position => C,
         Inserted => Inserted);

      Remapped_Cntexmp (C).Other_Lines.Include (VC_Line, VC);

      return (Remapped_Cntexmp);
   end Remap_VC_Info;

end Gnat2Why.Counter_Examples;
