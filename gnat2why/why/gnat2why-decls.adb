------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         G N A T 2 W H Y - D E C L S                      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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

with GNAT.Source_Info;

with Atree;                use Atree;
with Einfo;                use Einfo;
with Namet;                use Namet;
with Nlists;               use Nlists;
with Sem_Ch12;             use Sem_Ch12;
with Sem_Util;             use Sem_Util;
with Sinfo;                use Sinfo;
with Sinput;               use Sinput;
with String_Utils;         use String_Utils;

with SPARK_Definition;     use SPARK_Definition;
with SPARK_Util;           use SPARK_Util;

with Why.Ids;              use Why.Ids;
with Why.Sinfo;            use Why.Sinfo;
with Why.Atree.Accessors;  use Why.Atree.Accessors;
with Why.Atree.Mutators;   use Why.Atree.Mutators;
with Why.Atree.Builders;   use Why.Atree.Builders;
with Why.Gen.Decl;         use Why.Gen.Decl;
with Why.Gen.Names;        use Why.Gen.Names;
with Why.Gen.Binders;      use Why.Gen.Binders;
with Why.Gen.Expr;         use Why.Gen.Expr;
with Why.Types;            use Why.Types;
with Why.Conversions;      use Why.Conversions;

with Gnat2Why.Expr;        use Gnat2Why.Expr;
with Gnat2Why.Nodes;       use Gnat2Why.Nodes;
with Gnat2Why.Types;       use Gnat2Why.Types;
with Gnat2Why.Util;        use Gnat2Why.Util;

package body Gnat2Why.Decls is

   -----------------------------------
   -- Complete_Constant_Translation --
   -----------------------------------

   procedure Complete_Constant_Translation
     (File : in out Why_File;
      E    : Entity_Id)
   is
      Base_Name : constant String := Full_Name (E);
      Name      : constant String :=
        Base_Name & To_String (WNE_Constant_Closure);

   begin
      Open_Theory (File, Name,
                   Comment =>
                     "Module including all necessary axioms for the "
                       & "constant "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " declared at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  No filtering is necessary here, as the theory should on the contrary
      --  use the previously defined theory for the constant.
      --  Attach the newly created theory as a completion of the existing one.

      Close_Theory (File,
                    Filter_Entity  => Empty,
                    Defined_Entity => E,
                    Do_Closure     => True);
      Add_Completion (Base_Name, Name, File.Kind);
   end Complete_Constant_Translation;

   ------------------------
   -- Translate_Variable --
   ------------------------

   procedure Translate_Variable
     (File : in out Why_File;
      E     : Entity_Id)
   is
      Name : constant String := Full_Name (E);
      Decl : constant W_Declaration_Id :=
        (if Entity_In_SPARK (E) then
            New_Type
              (Name  => To_Ident (WNE_Type),
               Alias => +Why_Logic_Type_Of_Ada_Obj (E))
         else
            New_Type
              (Name => To_Ident (WNE_Type),
               Args => 0));
      Typ  : constant W_Primitive_Type_Id :=
        (if Ekind (E) = E_Loop_Parameter
         then New_Base_Type (Base_Type => EW_Int)
         else New_Abstract_Type (Name => Get_Name (W_Type_Id (Decl))));

      function Normalize_Type (E : Entity_Id) return Entity_Id;
      --  Choose the correct type to use

      --------------------
      -- Normalize_Type --
      --------------------

      function Normalize_Type (E : Entity_Id) return Entity_Id is
      begin
         if not (Ekind (E) in Private_Kind) or else
           Entity_In_External_Axioms (E)
         then
            return E;
         end if;
         if Entity_In_SPARK (Most_Underlying_Type (E)) then
            return Normalize_Type (Most_Underlying_Type (E));
         end if;
         return E;
      end Normalize_Type;

   begin
      Open_Theory (File, Name,
                   Comment =>
                     "Module for defining a ref holding the value of variable "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  Generate an alias for the name of the object's type, based on the
      --  name of the object. This is useful when generating logic functions
      --  from Ada functions, to generate additional parameters for the global
      --  objects read.

      Emit (File.Cur_Theory, Decl);

      if Entity_In_SPARK (Most_Underlying_Type (Etype (E))) then
         Add_Use_For_Entity (File, Normalize_Type (Etype (E)));
      end if;

      --  We generate a global ref

      Emit
        (File.Cur_Theory,
         New_Global_Ref_Declaration
           (Name     => To_Why_Id (E, Local => True),
            Ref_Type => Typ));

      Close_Theory (File, Filter_Entity => E, No_Import => True);
   end Translate_Variable;

   ------------------------
   -- Translate_Constant --
   ------------------------

   procedure Translate_Constant
     (File : in out Why_File;
      E    : Entity_Id)
   is
      Base_Name : constant String := Full_Name (E);
      Name      : constant String := Base_Name;
      Typ       : constant W_Primitive_Type_Id :=
        Why_Logic_Type_Of_Ada_Obj (E);

   begin
      --  Start with opening the theory to define, as the creation of a
      --  function for the logic term needs the current theory to insert an
      --  include declaration.

      Open_Theory (File, Name,
                   Comment =>
                     "Module for defining the constant "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  We generate a "logic", whose axiom will be given in a completion

      Emit (File.Cur_Theory,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => To_Why_Id (E, Domain => EW_Term, Local => True),
               Binders     => (1 .. 0 => <>),
               Return_Type => Typ));

      Close_Theory (File,
                    Filter_Entity  => E,
                    Defined_Entity => E);
   end Translate_Constant;

   ------------------------------
   -- Translate_Constant_Value --
   ------------------------------

   procedure Translate_Constant_Value
     (File : in out Why_File;
      E    : Entity_Id)
   is
      Base_Name : constant String := Full_Name (E);
      Name      : constant String :=
        Base_Name & To_String (WNE_Constant_Axiom);
      Typ    : constant W_Primitive_Type_Id := Why_Logic_Type_Of_Ada_Obj (E);
      Decl   : constant Node_Id := Parent (E);
      Def    : W_Term_Id;
      Ty_Ent : constant Entity_Id := Unique_Entity (Etype (E));
      Use_Ty : constant W_Base_Type_Id :=
        (if Is_Scalar_Type (Ty_Ent) then Base_Why_Type (Ty_Ent) else
            Type_Of_Node (E));

   begin
      --  Start with opening the theory to define, as the creation of a
      --  function for the logic term needs the current theory to insert an
      --  include declaration.

      Open_Theory (File, Name,
                   Comment =>
                     "Module for defining the value of constant "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  Default values of parameters are not considered as the value of the
      --  constant representing the parameter.

      if Ekind (E) /= E_In_Parameter
        and then Present (Expression (Decl))
      then
         Def := Get_Pure_Logic_Term_If_Possible
           (File, Expression (Decl), Use_Ty);
      else
         Def := Why_Empty;
      end if;

      if Def = Why_Empty then
         Discard_Theory (File);

      else
         --  The definition of constants is done in a separate theory. This
         --  theory is added as a completion of the base theory defining the
         --  constant.

         if Is_Full_View (E) then

            --  It may be the case that the full view has a more precise type
            --  than the partial view, for example when the type of the partial
            --  view is an indefinite array. In that case, convert back to the
            --  expected type for the constant.

            if Etype (Partial_View (E)) /= Etype (E) then
               Def := W_Term_Id (Insert_Conversion
                        (Domain   => EW_Term,
                         Ada_Node => Expression (Decl),
                         Expr     => W_Expr_Id (Def),
                         From     => Use_Ty,
                         To       => Type_Of_Node (Partial_View (E))));
            end if;

            Emit
              (File.Cur_Theory,
               New_Defining_Axiom
                 (Name        =>
                    To_Why_Id (E, Domain => EW_Term, Local => False),
                  Return_Type => Get_EW_Type (Typ),
                  Ada_Type    => Ty_Ent,
                  Binders     => (1 .. 0 => <>),
                  Def         => Def));

            --  No filtering is necessary here, as the theory should on the
            --  contrary use the previously defined theory for the partial
            --  view. Attach the newly created theory as a completion of the
            --  existing one.

            Close_Theory (File,
                          Filter_Entity  => Empty,
                          Defined_Entity => Partial_View (E));
            Add_Completion (Base_Name, Name, File.Kind);

         --  In the general case, we generate a defining axiom if necessary and
         --  possible.

         else
            Emit
              (File.Cur_Theory,
               New_Defining_Axiom
                 (Name        =>
                    To_Why_Id (E, Domain => EW_Term, Local => False),
                  Return_Type => Get_EW_Type (Typ),
                  Ada_Type    => Ty_Ent,
                  Binders     => (1 .. 0 => <>),
                  Def         => Def));

            --  No filtering is necessary here, as the theory should on the
            --  contrary use the previously defined theory for the partial
            --  view.

            Close_Theory (File,
                          Filter_Entity  => Empty,
                          Defined_Entity => E);
            Add_Completion (Base_Name, Name, File.Kind);
         end if;
      end if;
   end Translate_Constant_Value;

   --------------------------------------------
   -- Translate_Package_With_External_Axioms --
   --------------------------------------------

   procedure Translate_Package_With_External_Axioms
     (Package_Entity : Entity_Id) is
      type Entity_Array is array (Integer range <>) of Entity_Id;

      procedure Compute_Length (Labs         :     List_Id;
                                Subst_Length : out Natural;
                                Num_Of_Obj   : out Natural);
      --  Computes the length of the substitution that has to be computed
      --  for the parameters of the generic.

      procedure Parse_Declarations
        (Decls      : List_Id;
         File_Name  : String;
         Compl      : Entity_Array := (2 .. 1 => <>));
      --  Dispatches theories of SPARK entities of the package spec in the
      --  appropriate Why3 file. Since the copy of the Why3 axiomatization is
      --  in one single file, a copy of each theory needs to be added to the
      --  appropriate file afterward.

      procedure Parse_Parameters
        (Assoc         :     List_Id;
         Labs          :     List_Id;
         Generic_Name  :     String;
         Instance_Name :     String;
         Subst         : out W_Custom_Substitution_Array;
         Compl         : out Entity_Array);
      --  Creates a substitution for the generic parameters of the package
      --  if any. The substitution is a string following the format in
      --  GNAT.Regpat. It is then used to copy the associated Why3
      --  axiomatization.

      procedure Parse_Declarations
        (Decls      : List_Id;
         File_Name  : String;
         Compl      : Entity_Array := (2 .. 1 => <>)) is

         procedure Parse_Declaration
           (Node    : Node_Id);

         procedure Parse_Declaration
           (Node      : Node_Id) is
            E : constant Entity_Id := Defining_Entity (Node);
            Theory_Name : constant String := Full_Name (E);
            TFile : Why_File :=  Why_Files (Dispatch_Entity (E));
         begin

            --  If no theory is needed for Node there is nothing to do

            if not Entity_In_SPARK (E) then
               return;
            end if;

            --  Adds a new theory to the appropriate file, containing only a
            --  use export of the theory to be copied
            if TFile.Name.all /= File_Name then
               Open_Theory
                 (TFile, Theory_Name,
                  Comment => "Module for axiomatizing "
                  & """" & Get_Name_String (Chars (E)) & """"
                  & (if Sloc (E) > 0 then
                       " defined at " & Build_Location_String (Sloc (E))
                    else "")
                  & ", created in " & GNAT.Source_Info.Enclosing_Entity);

               Add_With_Clause (T        => TFile.Cur_Theory,
                                File     => File_Name,
                                T_Name   => Capitalize_First (Theory_Name),
                                Use_Kind => EW_Export);

               if not (Ekind (E) in Type_Kind) then
                  for I in Compl'Range loop
                     Add_Completion (Name            => Full_Name (E),
                                     Completion_Name => Full_Name (Compl (I)),
                                     Kind            =>
                                       Dispatch_Entity (Compl (I)));
                  end loop;
               end if;

               Close_Theory (TFile, Filter_Entity => Empty);
            end if;

            if Ekind (E) in Subprogram_Kind then
               declare
                  File : Why_File := Why_Files (Dispatch_Entity (E));
               begin
                  Open_Theory (File,
                               Theory_Name & To_String (WNE_Expr_Fun_Closure),
                               Comment => "");

                  Close_Theory (File,
                                Filter_Entity  => Empty,
                                Defined_Entity => E,
                                Do_Closure     => True);
               end;
            end if;
         end Parse_Declaration;

         Cur : Node_Id := First (Decls);
      begin

         --  Call Parse_Declaration on every element of the list of
         --  declarations that needs a translation.

         while Present (Cur) loop
            if Comes_From_Source (Cur) and then
              Nkind (Cur) in N_Subtype_Declaration | N_Private_Type_Declaration
              | N_Subprogram_Declaration | N_Object_Declaration then
               Parse_Declaration (Cur);
            end if;
            Next (Cur);
         end loop;
      end Parse_Declarations;

      procedure Compute_Length (Labs         :     List_Id;
                                Subst_Length : out Natural;
                                Num_Of_Obj   : out Natural) is
         CurLabs  : Node_Id := First (Labs);
      begin
         Subst_Length := 1;
         Num_Of_Obj   := 0;
         while Present (CurLabs) loop
            declare
               K : constant Entity_Kind :=
                 Ekind (Defining_Entity (CurLabs));
            begin
               if K in Private_Kind then
                  Subst_Length := Subst_Length + 6;
               elsif K in Type_Kind then
                  Subst_Length := Subst_Length + 3;
               else
                  Num_Of_Obj   := Num_Of_Obj + 1;
                  Subst_Length := Subst_Length + 2;
               end if;
            end;
            Next (CurLabs);
         end loop;
      end Compute_Length;

      procedure Parse_Parameters
        (Assoc         :     List_Id;
         Labs          :     List_Id;
         Generic_Name  :     String;
         Instance_Name :     String;
         Subst         : out W_Custom_Substitution_Array;
         Compl         : out Entity_Array) is

         --  Names of elements expected in a Why3 theory for a formal of a
         --  private type. Used to comply with the special handling for
         --  range types. In parameters of subprograms are expected to be of
         --  type Base_Type_Name. The functions To_Base_Name and Of_Base_Name
         --  are used to translate to and from type Base_Type_Name and
         --  the predicate In_Range_Name asserts that an element of type
         --  Base_Type_Name can be translated back to the range type.

         Base_Type_Name : constant String := "base_type";
         To_Base_Name   : constant String := "to_base";
         Of_Base_Name   : constant String := "of_base";
         In_Range_Name  : constant String := "valid";

         TFile     : Why_File := Why_Files (Dispatch_Entity (Package_Entity));
         File_Name : constant String := TFile.Name.all;
         CurAssoc  : Node_Id := First (Assoc);
         CurLabs   : Node_Id := First (Labs);
         Subst_Cur : Integer := 1;
         Compl_Cur : Integer := 1;
      begin
         while Present (CurAssoc) loop
            declare
               Actual : constant Entity_Id :=
                 Entity (Explicit_Generic_Actual_Parameter (CurAssoc));
               Formal : constant Entity_Id := Defining_Entity (CurLabs);
               Actual_File : constant String :=
                 File_Base_Name_Of_Entity (Actual)
                 & Why_File_Suffix (Dispatch_Entity (Actual));
            begin

               --  Replace:
               --  use "<Generic_Name>__args".<Generic_Name>__<Formal>
               --  by: use ("<Actual_File>".)Name_Of_Node (Actual)
               --  No use is generated if Actual doesn't have a unique name

               if Full_Name_Is_Not_Unique_Name (Actual) then
                  Subst (Subst_Cur) := New_Custom_Substitution
                    (Domain   => EW_Prog,
                     From     => NID ("use\s+" & """" & Generic_Name &
                         "__args""\." & Capitalize_First (Generic_Name) & "__"
                       & Short_Name (Formal) & "\s"),
                     To       => W_Any_Node_Id (
                       New_Identifier (Name => "" & ASCII.LF)));

               elsif Actual_File /= File_Name then
                  Subst (Subst_Cur) := New_Custom_Substitution
                    (Domain   => EW_Prog,
                     From     => NID ("use\s+" & """" & Generic_Name &
                         "__args""\." & Capitalize_First (Generic_Name) & "__"
                       & Short_Name (Formal) & "\s"),
                     To       => W_Any_Node_Id (New_Identifier
                       (Name => "use """ & Actual_File & """." &
                          Capitalize_First (Name_Of_Node (Actual))
                        & ASCII.LF)));
               else
                  Subst (Subst_Cur) := New_Custom_Substitution
                    (Domain   => EW_Prog,
                     From     => NID ("use\s+" & """" & Generic_Name &
                         "__args""\." & Capitalize_First (Generic_Name) & "__"
                       & Short_Name (Formal) & "\s"),
                     To       => W_Any_Node_Id (New_Identifier
                       (Name => "use " & Capitalize_First
                        (Name_Of_Node (Actual)) & ASCII.LF)));
               end if;
               Subst_Cur := Subst_Cur + 1;

               --  For types, replace: <Generic_Name>__<Formal>.<Formal>
               --  by: Why_Logic_Type_Of_Ada_Type (Actual)

               if Ekind (Formal) in Type_Kind then

                  --  For type parameters, generate a theory that renames the
                  --  theory of the actual. Necessary for conversion functions.

                  Open_Theory
                    (TFile, Capitalize_First (Instance_Name) & "__"
                     & Short_Name (Formal),
                     Comment => "");

                  Add_Use_For_Entity
                    (P               => TFile,
                     N               => Actual,
                     Use_Kind        => EW_Export,
                     With_Completion => False);

                  if Short_Name (Formal) /= Short_Name (Actual) then
                     Emit
                       (TFile.Cur_Theory,
                        New_Type
                          (Name  =>
                             New_Identifier (Name => Short_Name (Formal)),
                           Alias => Why_Logic_Type_Of_Ada_Type (Actual)));
                  end if;

                  Close_Theory (TFile, Filter_Entity => Empty);

                  Subst (Subst_Cur) := New_Custom_Substitution
                    (Domain   => EW_Prog,
                     From     => NID (Capitalize_First (Generic_Name)
                       & "__" & Short_Name (Formal) & "\." &
                         Short_Name (Formal)),
                     To       => W_Any_Node_Id
                       (Why_Logic_Type_Of_Ada_Type (Actual)));

                  --  If the formal has a private kind, Base_Type_Name,
                  --  To_Base_Name, Of_Base_Name, and In_Range_Name must be
                  --  replaced appropriately

                  if Ekind (Formal) in Private_Kind then
                     declare
                        Actual_Type : constant W_Primitive_Type_OId :=
                          Why_Logic_Type_Of_Ada_Type (Actual);
                        Actual_Base : constant W_Primitive_Type_OId :=
                          +Base_Why_Type (Actual);
                     begin

                        --  If the actual is a scalar type and not a boolean:
                        --  <Generic_Name>__<Base_Type_Name> =>
                        --               Base_Why_Type (<Actual>)
                        --  <Generic_Name>__<To_Base_Name>   =>
                        --               Conversion_Name (To   => <Base>,
                        --                                From => <Actual>)
                        --  <Generic_Name>__<Of_Base_Name>   =>
                        --               Conversion_Name (From => <Base>,
                        --                                To   => <Actual>)
                        --  <Generic_Name>__<In_Range_Name>  =>
                        --               Range_Pred_Name (<Actual>)
                        --  Otherwise:
                        --  <Generic_Name>__<Base_Type_Name> => <Actual>
                        --  <Generic_Name>__<To_Base_Name>   =>
                        --  <Generic_Name>__<Of_Base_Name>   =>
                        --  <Generic_Name>__<In_Range_Name>  => __ignore

                        if Is_Scalar_Type (Actual) and then
                          not Is_Boolean_Type (Actual) then
                           Subst (Subst_Cur + 1) := New_Custom_Substitution
                             (Domain   => EW_Prog,
                              From     => NID (Capitalize_First (Generic_Name)
                                & "__" & Short_Name (Formal) & "\." &
                                  Base_Type_Name),
                              To       => W_Any_Node_Id (Actual_Base));

                           Subst (Subst_Cur + 2) := New_Custom_Substitution
                             (Domain   => EW_Prog,
                              From     => NID (Capitalize_First (Generic_Name)
                                & "__" & Short_Name (Formal) & "\." &
                                  To_Base_Name),
                              To       => W_Any_Node_Id (Conversion_Name
                                (From => +Actual_Type,
                                 To => +Actual_Base)));

                           Subst (Subst_Cur + 3) := New_Custom_Substitution
                             (Domain   => EW_Prog,
                              From     => NID (Capitalize_First (Generic_Name)
                                & "__" & Short_Name (Formal) & "\." &
                                  Of_Base_Name),
                              To       => W_Any_Node_Id (Conversion_Name
                                (From => +Actual_Base,
                                 To => +Actual_Type)));

                           Subst (Subst_Cur + 4) := New_Custom_Substitution
                             (Domain   => EW_Prog,
                              From     => NID (Capitalize_First (Generic_Name)
                                & "__" & Short_Name (Formal) & "\." &
                                  In_Range_Name),
                              To       => W_Any_Node_Id
                                (Range_Pred_Name (Actual)));
                        else
                           Subst (Subst_Cur + 1) := New_Custom_Substitution
                             (Domain   => EW_Prog,
                              From     => NID (Capitalize_First (Generic_Name)
                                & "__" & Short_Name (Formal) & "\." &
                                  Base_Type_Name),
                              To       => W_Any_Node_Id (Actual_Type));

                           Subst (Subst_Cur + 2) := New_Custom_Substitution
                             (Domain   => EW_Prog,
                              From     => NID (Capitalize_First (Generic_Name)
                                & "__" & Short_Name (Formal) & "\." &
                                  To_Base_Name),
                              To       => W_Any_Node_Id
                                (New_Identifier (Name => "")));

                           Subst (Subst_Cur + 3) := New_Custom_Substitution
                             (Domain   => EW_Prog,
                              From     => NID (Capitalize_First (Generic_Name)
                                & "__" & Short_Name (Formal) & "\." &
                                  Of_Base_Name),
                              To       => W_Any_Node_Id
                                (New_Identifier (Name => "")));

                           Subst (Subst_Cur + 4) := New_Custom_Substitution
                             (Domain   => EW_Prog,
                              From     => NID (Capitalize_First (Generic_Name)
                                & "__" & Short_Name (Formal) & "\." &
                                  In_Range_Name),
                              To       => W_Any_Node_Id
                                (New_Identifier (Name => "__ignore")));
                        end if;
                     end;
                     Subst_Cur := Subst_Cur + 5;
                  else

                     --  If the formal is not of a private kind, there can be
                     --  some other elements in its module that are used
                     --  inside the axiomatization.
                     --  Replace: <Generic_Name>__<Formal>.
                     --  by: Name_Of_Node (Actual).

                     Subst (Subst_Cur + 1) := New_Custom_Substitution
                       (Domain   => EW_Prog,
                        From     => NID (Capitalize_First (Generic_Name)
                          & "__" & Short_Name (Formal) & "\."),
                        To       => W_Any_Node_Id
                          (New_Identifier (Name => Capitalize_First
                                           (Name_Of_Node (Actual)) & ".")));
                     Subst_Cur := Subst_Cur + 2;
                  end if;

                  --  For functions and objects,
                  --  replace: <Generic_Name>__<Formal>.<Formal>
                  --  by: To_Why_Id (Actual)

               else
                  Compl (Compl_Cur) := Actual;
                  Compl_Cur := Compl_Cur + 1;

                  Subst (Subst_Cur) := New_Custom_Substitution
                    (Domain   => EW_Prog,
                     From     => NID (Capitalize_First (Generic_Name)
                       & "__" & Short_Name (Formal) & "\." &
                         Short_Name (Formal)),
                     To       => W_Any_Node_Id
                       (To_Why_Id (Actual, Domain => EW_Term)));
                  Subst_Cur := Subst_Cur + 1;
               end if;
            end;
            Next (CurAssoc);
            Next (CurLabs);
         end loop;

         --  A last substitution is needed to rename every module in the copy
         --  so that there is no name clash.
         --  Replace: <Generic_Name>__ by: <Instance_Name>__

         Subst (Subst_Cur) := New_Custom_Substitution
           (Domain   => EW_Prog,
            From     => NID (Capitalize_First (Generic_Name) & "__"),
            To       => W_Any_Node_Id
              (New_Identifier (Name => Instance_Name & "__")));
      end Parse_Parameters;

      Decls : constant List_Id :=
        Visible_Declarations (Parent (Package_Entity));
      G_Node : constant Node_Id :=
        Generic_Parent (Parent (Package_Entity));
      TFile : constant Why_File :=
        Why_Files (Dispatch_Entity (Package_Entity));
   begin
      if Present (G_Node) then
         declare
            Generic_Name : constant String :=
              Full_Name (G_Node);
            Instance_Name : constant String :=
              Capitalize_First (Full_Name (Package_Entity));
            Assoc : constant List_Id := Generic_Associations
              (Get_Package_Instantiation_Node (Package_Entity));

            --  use Parent field to reach N_Generic_Package_Declaration

            Labs : constant List_Id :=
              Generic_Formal_Declarations (Parent (Parent (Parent (G_Node))));
            Subst_Length : Natural;
            Num_Of_Compl : Natural;
         begin
            Compute_Length (Labs, Subst_Length, Num_Of_Compl);
            declare
               Subst : W_Custom_Substitution_Array (1 .. Subst_Length);
               Compl : Entity_Array (1 .. Num_Of_Compl);
            begin
               Parse_Parameters
                 (Assoc, Labs, Generic_Name, Instance_Name, Subst, Compl);

               File_Append_To_Theories
                 (TFile.File, New_Custom_Declaration
                    (Domain    => EW_Prog,
                     File_Name => NID (Generic_Name & ".mlw"),
                     Subst     => Subst));

               Parse_Declarations (Decls, TFile.Name.all, Compl);
            end;
         end;
      else
         File_Append_To_Theories
           (TFile.File, New_Custom_Declaration
              (Domain    => EW_Prog,
               File_Name => NID (Full_Name (Package_Entity) & ".mlw")));

         Parse_Declarations (Decls, TFile.Name.all);
      end if;
   end Translate_Package_With_External_Axioms;

   ---------------------------
   -- Translate_Loop_Entity --
   ---------------------------

   procedure Translate_Loop_Entity
     (File : in out Why_File;
      E    : Entity_Id)
   is
      Name : constant String := Full_Name (E);
   begin
      Open_Theory (File, Name,
                   Comment =>
                     "Module for defining the loop exit exception for the loop"
                   & """" & Get_Name_String (Chars (E)) & """"
                   & (if Sloc (E) > 0 then
                     " defined at " & Build_Location_String (Sloc (E))
                     else "")
                   & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Emit (File.Cur_Theory,
            New_Exception_Declaration (Name => To_Why_Id (E, Local => True),
                                       Arg  => Why_Empty));

      Close_Theory (File, Filter_Entity => E, No_Import => True);
   end Translate_Loop_Entity;

   -----------------------
   -- Use_Why_Base_Type --
   -----------------------

   function Use_Why_Base_Type (E : Entity_Id) return Boolean
   is
      Ty : constant Entity_Id := Etype (E);
   begin
      return not Is_Mutable_In_Why (E) and then
        Is_Scalar_Type (Ty) and then
        not Is_Boolean_Type (Ty);
   end Use_Why_Base_Type;

end Gnat2Why.Decls;
