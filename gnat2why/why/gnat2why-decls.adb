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
with Sinfo;                use Sinfo;
with Sinput;               use Sinput;

with SPARK_Definition;     use SPARK_Definition;
with SPARK_Util;           use SPARK_Util;

with Why.Ids;              use Why.Ids;
with Why.Sinfo;            use Why.Sinfo;
with Why.Atree.Accessors;  use Why.Atree.Accessors;
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

with Sem_Ch12;             use Sem_Ch12;
with String_Utils;         use String_Utils;
with Namet;                use Namet;
with Nlists;               use Nlists;
with Sem_Util;             use Sem_Util;
with Gnat2Why.Subprograms; use Gnat2Why.Subprograms;
with Why.Gen.Terms;        use Why.Gen.Terms;

package body Gnat2Why.Decls is

   -----------------------------------
   -- Complete_Constant_Translation --
   -----------------------------------

   procedure Complete_Constant_Translation
     (File    : in out Why_File;
      E       : Entity_Id;
      In_Body : Boolean)
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

      if In_Body then
         Add_Completion (Base_Name, Name, WF_Context_In_Body);
      else
         Add_Completion (Base_Name, Name, WF_Context_In_Spec);
      end if;
   end Complete_Constant_Translation;

   ----------------
   -- Is_Mutable --
   ----------------

   function Is_Mutable_In_Why (N : Node_Id) return Boolean
   is
   begin

      --  A variable is translated as mutable in Why if it is not constant on
      --  the Ada side, or if it is a loop parameter (of an actual loop, not a
      --  quantified expression.

      if Ekind (N) = E_Loop_Parameter then
         return not (Is_Quantified_Loop_Param (N));
      elsif Ekind (N) = E_Enumeration_Literal or else
        Is_Constant_Object (N) or else
        Ekind (N) in Named_Kind then
         return False;
      else
         return True;
      end if;
   end Is_Mutable_In_Why;

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
           Type_In_Formal_Container (E)
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
     (File   : in out Why_File;
      E      : Entity_Id)
   is
      Base_Name : constant String := Full_Name (E);
      Name      : constant String :=
                    (if Is_Full_View (E) then
                       Base_Name & To_String (WNE_Constant_Axiom)
                     else
                       Base_Name);
      Typ  : constant W_Primitive_Type_Id := Why_Logic_Type_Of_Ada_Obj (E);
      Decl : constant Node_Id := Parent (E);
      Def  : W_Term_Id;

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
           (File, Expression (Decl), Type_Of_Node (E));
      else
         Def := Why_Empty;
      end if;

      --  The definition of deferred constants is done in a separate theory, so
      --  that only code in the unit defining the deferred constant has access
      --  to its value. This allows supporting parameterized verification of
      --  client units not depending on the value of a delayed constant. This
      --  theory is added as a completion of the base theory defining the
      --  constant, so that further modules including the base theory also
      --  include the completion, for modules defined in this unit. Theories
      --  defined in other units only have access to the base theory. Note
      --  that modules in the same unit may also have access to the base
      --  theory only, if they are defined before this point.

      if Is_Full_View (E) then
         if Def = Why_Empty then
            Discard_Theory (File);

         else
            --  It may be the case that the full view has a more precise type
            --  than the partial view, for example when the type of the partial
            --  view is an indefinite array. In that case, convert back to the
            --  expected type for the constant.

            if Etype (Partial_View (E)) /= Etype (E) then
               Def := W_Term_Id (Insert_Conversion
                        (Domain   => EW_Term,
                         Ada_Node => Expression (Decl),
                         Expr     => W_Expr_Id (Def),
                         From     => Type_Of_Node (E),
                         To       => Type_Of_Node (Partial_View (E))));
            end if;

            Emit
              (File.Cur_Theory,
               New_Defining_Axiom
                 (Name        =>
                    To_Why_Id (E, Domain => EW_Term, Local => False),
                  Return_Type => Get_EW_Type (Typ),
                  Binders     => (1 .. 0 => <>),
                  Def         => Def));

            --  No filtering is necessary here, as the theory should on the
            --  contrary use the previously defined theory for the partial
            --  view. Attach the newly created theory as a completion of the
            --  existing one.

            Close_Theory (File,
                          Filter_Entity  => Empty,
                          Defined_Entity => Partial_View (E));

            if In_Main_Unit_Body (E) then
               Add_Completion (Base_Name, Name, WF_Context_In_Body);
            else
               Add_Completion (Base_Name, Name, WF_Context_In_Spec);
            end if;
         end if;

      --  In the general case, we generate a "logic", with a defining axiom if
      --  necessary and possible.

      else
         Emit
           (File.Cur_Theory,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => To_Why_Id (E, Domain => EW_Term, Local => True),
               Binders     => (1 .. 0 => <>),
               Return_Type => Typ));

         if Def /= Why_Empty then
            Emit
              (File.Cur_Theory,
               New_Defining_Axiom
                 (Name        =>
                    To_Why_Id (E, Domain => EW_Term, Local => True),
                  Return_Type => Get_EW_Type (Typ),
                  Binders     => (1 .. 0 => <>),
                  Def         => Def));
         end if;

         Close_Theory (File,
                       Filter_Entity  => E,
                       Defined_Entity => E);
      end if;
   end Translate_Constant;

   ---------------------------------
   -- Translate_Container_Package --
   ---------------------------------

   procedure Translate_Container_Package (Package_Entity : Entity_Id) is

      procedure Parse_Declarations
        (Decls      : List_Id;
         Clone_Name : String);
      --  Generates a theory per SPARK entity of the package spec. Each
      --  theories should define every why element that is expected by the
      --  usual translation mechanism so that belonging to an axiomatized
      --  package is transparent.

      function Parse_Parameters
        (Assoc      : List_Id;
         Labs       : List_Id;
         Clone_Name : String) return W_Clone_Substitution_Array;
      --  Creates the substitution for the generic parameter
      --  The substitution is then used to clone the axiomatization

      procedure Parse_Declarations
        (Decls      : List_Id;
         Clone_Name : String) is

         procedure Parse_Declaration
           (Node    : Node_Id);

         procedure Parse_Declaration
           (Node    : Node_Id) is
         begin
            case Nkind (Node) is
            when N_Subtype_Declaration | N_Private_Type_Declaration =>
               --  Generates the type definition and an access function per
               --  discriminant if any.
               --  No equality function is needed.
               --  Only works for private types with discriminants.
               if not Comes_From_Source (Node) then
                  return;
               end if;
               declare
                  E : constant Entity_Id := Defining_Identifier (Node);
                  Id : constant W_Identifier_Id :=
                    To_Why_Id (E, Domain => EW_Term, Local => True);
                  Type_Name : constant String := Short_Name (E);
                  Theory_Name : constant String := Full_Name (E);
                  TFile : Why_File :=
                    Why_Files (Dispatch_Entity (E));
                  Corresponding_Type : constant W_Primitive_Type_Id :=
                    New_Abstract_Type
                    (Name => New_Identifier (Name => Type_Name,
                                             Context => Clone_Name));
                  Binder : constant Binder_Type :=
                    Binder_Type'(B_Name =>
                                   New_Identifier (Name => Type_Name & "__x"),
                                 B_Type => Corresponding_Type,
                                 others => <>);
               begin
                  if not Entity_In_SPARK (E) then
                     return;
                  end if;
                  --  Ada.Text_IO.Put_Line ("New type : " & Type_Name);

                  Open_Theory
                    (TFile, Theory_Name,
                     Comment => "Module for axiomatizing type "
                     & """" & Get_Name_String (Chars (E)) & """"
                     & (if Sloc (E) > 0 then
                       " defined at " & Build_Location_String (Sloc (E))
                       else "")
                     & ", created in " & GNAT.Source_Info.Enclosing_Entity);

                  Add_Use_For_Entity (TFile, Package_Entity);

                  --  type <type> = <type>
                  Emit
                    (TFile.Cur_Theory,
                     New_Type (Ada_Node   => Node,
                               Name       => Id,
                               Definition =>
                                 New_Transparent_Type_Definition
                                   (Domain          => EW_Term,
                                    Type_Definition => Corresponding_Type)));

                  if Ekind (E) in Integer_Kind then
                     Emit
                       (TFile.Cur_Theory,
                        New_Function_Def
                          (Domain      => EW_Term,
                           Name        => To_Ident (WNE_To_Int),
                           Binders     => (1 .. 1 => Binder),
                           Return_Type => New_Base_Type (Base_Type => EW_Int),
                           Def         =>
                             New_Call
                               (Domain   => EW_Term,
                                Binders  => (1 .. 1 => Binder),
                                Name     =>
                                  New_Identifier (Name => Type_Name & "__" &
                                                    To_String (WNE_To_Int),
                                                  Context => Clone_Name))));
                     Emit
                       (TFile.Cur_Theory,
                        New_Function_Def
                          (Domain      => EW_Term,
                           Name        => To_Ident (WNE_Of_Int),
                           Binders     =>
                             (1 .. 1 =>
                                Binder_Type'(
                                  B_Name => New_Identifier
                                    (Name => Type_Name & "__x"),
                                  B_Type => New_Base_Type
                                    (Base_Type => EW_Int),
                                  others => <>)),
                           Return_Type => Corresponding_Type,
                           Def         =>
                             New_Call
                               (Domain   => EW_Term,
                                Binders  => (1 .. 1 => Binder),
                                Name     =>
                                  New_Identifier (Name => Type_Name & "__" &
                                                    To_String (WNE_Of_Int),
                                                  Context => Clone_Name))));
                  end if;

                  if Nkind (Node) = N_Private_Type_Declaration
                    and then Present (Discriminant_Specifications (Node))
                  then
                     declare
                        Curs : Node_Id :=
                          First (Discriminant_Specifications (Node));
                     begin
                        --  Iterates over the discriminants
                        while Present (Curs) loop
                           declare
                              E : constant Entity_Id :=
                                Defining_Identifier (Curs);
                              Name : constant String := Short_Name (E);
                              Logic_Id : constant W_Identifier_Id :=
                                To_Why_Id (E, Local => True);
                              Program_Id : constant W_Identifier_Id :=
                                To_Program_Space (Logic_Id);
                              Discr_Type : constant W_Primitive_Type_Id :=
                                Why_Logic_Type_Of_Ada_Obj (E);
                              Associated_Fun : constant W_Identifier_Id :=
                                New_Identifier (Name => Type_Name & "__" &
                                                  Name & "__record",
                                                Context => Clone_Name);
                           begin
                              --  val rec_<field>_ (<type>_x : <type>):
                              --                              <dicr_type>
                              --  ensures
                              --  { result = <type>_<field>_record <type>_x }
                              Emit
                                (TFile.Cur_Theory,
                                 New_Function_Decl
                                   (Domain      => EW_Prog,
                                    Name        => Program_Id,
                                    Binders     => (1 .. 1 => Binder),
                                    Return_Type => Discr_Type,
                                    Pre         => Why_Empty,
                                    Post        => New_Relation
                                      (Op      => EW_Eq,
                                       Op_Type => EW_Bool,
                                       Left    => +To_Ident (WNE_Result),
                                       Right   =>
                                         +New_Call (Domain   => EW_Term,
                                                   Binders  =>
                                                     (1 .. 1 => Binder),
                                                   Name     =>
                                                      Associated_Fun))));

                              --  function rec_<field> (<type>_x : <type>):
                              --                                <dicr_type> =
                              --         <type>_<field>_record <type>_x
                              Emit
                                (TFile.Cur_Theory,
                                 New_Function_Def
                                   (Domain      => EW_Term,
                                    Name        => Logic_Id,
                                    Binders     => (1 .. 1 => Binder),
                                    Return_Type => Discr_Type,
                                    Def         =>
                                      New_Call (Domain   => EW_Term,
                                                Binders  => (1 .. 1 => Binder),
                                                Name     => Associated_Fun)));
                              Next (Curs);
                           end;
                        end loop;
                     end;
                  end if;
                  Close_Theory (TFile, Filter_Entity => E,
                                Defined_Entity => E);
               end;

            when N_Subprogram_Declaration
               | N_Subprogram_Renaming_Declaration =>
               if not Comes_From_Source (Node) then
                  return;
               end if;
               declare
                  Spec  : constant Node_Id := Specification (Node);
                  E : constant Entity_Id := Defining_Entity (Node);
                  Name : constant String := Short_Name (E);
                  Program_Id : constant W_Identifier_Id :=
                    To_Why_Id (E, Domain => EW_Prog, Local => True);
                  Theory_Name : constant String := Full_Name (E);
                  TFile : Why_File :=
                    Why_Files (Dispatch_Entity (E));
                  Pre_Fun : constant W_Identifier_Id :=
                    New_Identifier (Name => Name & "__pre",
                                    Context => Clone_Name);
                  Post_Fun : constant W_Identifier_Id :=
                    New_Identifier (Name => Name & "__post",
                                    Context => Clone_Name);
                  Return_Type : constant W_Primitive_Type_Id :=
                    (if Ekind (E) = E_Function then
                       Why_Logic_Type_Of_Ada_Type (Etype (E))
                     else New_Base_Type (Base_Type => EW_Unit));
                  Binders : constant Binder_Array := Compute_Binders (E);
                  Pre_Args : W_Expr_Array (Binders'Range);
                  Post_Args : W_Expr_Array (1 .. 2 * (Binders'Length) + 1);
                  Args_Length : Integer := 0;
                  RW : W_Identifier_Array (Binders'Range);
                  RW_Length : Integer := 0;
               begin
                  for J in Binders'Range loop
                     Args_Length := Args_Length + 1;
                     if Binders (J).Modifier = Ref_Modifier then
                        Post_Args (Args_Length) :=
                          New_Deref (Right => Binders (J).B_Name);
                        Pre_Args (J) :=
                          New_Deref (Right => Binders (J).B_Name);
                        Args_Length := Args_Length + 1;
                        Post_Args (Args_Length) :=
                          New_Old (New_Deref (Right => Binders (J).B_Name),
                                   EW_Term);
                        RW_Length := RW_Length + 1;
                        RW (RW_Length) := Binders (J).B_Name;
                     else
                        Post_Args (Args_Length) := +Binders (J).B_Name;
                        Pre_Args (J) := +Binders (J).B_Name;
                     end if;
                  end loop;
                  if Ekind (E) = E_Function then
                     Args_Length := Args_Length + 1;
                     Post_Args (Args_Length) := +To_Ident (WNE_Result);
                  end if;
--                    Ada.Text_IO.Put_Line ("New function : " & Name);

                  --  Store the source entity corresponding to the function
                  --  Has_Element for this particular type of container,
                  --  for use in translating quantification over this
                  --  container's type.

                  if Name = SPARK_Util.Lowercase_Has_Element_Name then
                     declare
                        Container_Type : constant Entity_Id :=
                          Etype (Defining_Identifier
                                 (First (Parameter_Specifications (Spec))));
                     begin
                        Gnat2Why.Expr.Container_Type_To_Has_Element_Function
                          .Insert (Container_Type, E);
                     end;
                  end if;

                  Open_Theory
                    (TFile, Theory_Name,
                     Comment =>
                       "Module for declaring a program function (and possibly "
                     & "a logic function) for "
                     & """" & Get_Name_String (Chars (E)) & """"
                     & (if Sloc (E) > 0 then
                       " defined at " & Build_Location_String (Sloc (E))
                       else "")
                     & ", created in " & GNAT.Source_Info.Enclosing_Entity);

                  --  val <func_name> (x : ref t, y: t) : t
                  --  ensures <func_name>_post (x, old x, y, result)
                  --  requires <func_name>_pre (x, y)
                  --  reads x
                  --  writes x
                  declare
                     Pre_Pred : constant W_Expr_Id :=
                       New_Call (Domain => EW_Term,
                                 Name   => Pre_Fun,
                                 Args   => Pre_Args);
                     Post_Pred : constant W_Expr_Id :=
                       New_Call (Domain => EW_Term,
                                 Name   => Post_Fun,
                                 Args   => Post_Args (1 .. Args_Length));
                  begin
                     Emit
                       (TFile.Cur_Theory,
                        New_Function_Decl
                          (Domain      => EW_Prog,
                           Name        => Program_Id,
                           Binders     => Binders,
                           Return_Type => Return_Type,
                           Effects     => New_Effects
                             (Reads  => RW (1 .. RW_Length),
                              Writes => RW (1 .. RW_Length)),
                           Pre         => +Pre_Pred,
                           Post        => +Post_Pred));
                  end;

                  if Ekind (E) = E_Function then
                     declare
                        Logic_Fun : constant W_Identifier_Id :=
                          New_Identifier (Name => Name & "__logic",
                                          Context => Clone_Name);
                        Logic_Id : constant W_Identifier_Id :=
                          To_Why_Id (E, Domain => EW_Term, Local => True);
                     begin
                        --  function func (...) = <func_name>__logic (...)
                        Emit
                          (TFile.Cur_Theory,
                           New_Function_Def
                             (Domain      => EW_Term,
                              Name        => Logic_Id,
                              Binders     => Binders,
                              Return_Type => Return_Type,
                              Def         =>
                                New_Call (Domain   => EW_Term,
                                          Binders  => Binders,
                                          Name     => Logic_Fun),
                              Pre         => Why_Empty,
                              Post        => Why_Empty));
                     end;
                  end if;

                  Add_Use_For_Entity (TFile, Package_Entity);
                  Close_Theory (TFile, Filter_Entity => E,
                                Defined_Entity => E);
               end;

            when N_Object_Declaration =>
               if not Comes_From_Source (Node) then
                  return;
               end if;
               declare
                  E : constant Entity_Id := Defining_Entity (Node);
                  Theory_Name : constant String := Full_Name (E);
                  Name : constant String := Short_Name (E);
                  Typ  : constant W_Primitive_Type_Id :=
                    Why_Logic_Type_Of_Ada_Obj (E);
                  Def : constant W_Identifier_Id :=
                    New_Identifier (Name => Name & "__object",
                                    Context => Clone_Name);
                  TFile : Why_File :=
                    Why_Files (Dispatch_Entity (E));
               begin
                  if not Entity_In_SPARK (E) then
                     return;
                  end if;

                  --  Ada.Text_IO.Put_Line ("New constant : " & Name);

                  Open_Theory
                    (TFile, Theory_Name,
                     Comment =>
                       "Module for defining the value of constant "
                     & """" & Get_Name_String (Chars (E)) & """"
                     & (if Sloc (E) > 0 then
                       " defined at " & Build_Location_String (Sloc (E))
                       else "")
                     & ", created in " & GNAT.Source_Info.Enclosing_Entity);

                  --  function func = <obj_name>__object
                  Emit
                    (TFile.Cur_Theory,
                     New_Function_Def
                       (Domain      => EW_Term,
                        Name        =>
                          To_Why_Id (E, Domain => EW_Term, Local => True),
                        Binders     => (1 .. 0 => <>),
                        Def         => +Def,
                        Return_Type => Typ));

                  Add_Use_For_Entity (TFile, Package_Entity);

                  Close_Theory (TFile, Filter_Entity => E);
               end;
            when others => null;
            end case;
         end Parse_Declaration;

         Cur : Node_Id := First (Decls);
      begin
         while Present (Cur) loop
            Parse_Declaration (Cur);
            Next (Cur);
         end loop;
      end Parse_Declarations;

      function Parse_Parameters
        (Assoc      : List_Id;
         Labs       : List_Id;
         Clone_Name : String) return W_Clone_Substitution_Array is

         function Get_Assoc_From_Param
           (CurAssoc : Node_Id;
            CurLabs  : Node_Id) return Node_Id;

         function Subst_Length (Assoc : List_Id;
                                Labs  : List_Id) return Integer;

         function Get_Assoc_From_Param
           (CurAssoc : Node_Id;
            CurLabs  : Node_Id) return Node_Id is
            Potential_Assoc : constant Node_Id  :=
              Selector_Name (CurAssoc);
         begin
            if Present (Potential_Assoc) then
               return Entity (Potential_Assoc);
            else
               return Defining_Entity (CurLabs);
            end if;
         end Get_Assoc_From_Param;

         function Subst_Length (Assoc : List_Id;
                                Labs  : List_Id) return Integer is
            Current  : Integer := 0;
            CurAssoc : Node_Id := First (Assoc);
            CurLabs  : Node_Id := First (Labs);
         begin
            while Present (CurAssoc) loop
               case Ekind (Get_Assoc_From_Param (CurAssoc, CurLabs)) is
                  when Integer_Kind => Current := Current + 5;
                  when others => Current := Current + 1;
               end case;
               Next (CurAssoc);
               Next (CurLabs);
            end loop;
            while Present (CurLabs) loop
               Current := Current + 1;
               Next (CurLabs);
            end loop;
            return Current;
         end Subst_Length;

         CurAssoc : Node_Id;
         CurLabs  : Node_Id;
         Current  : Integer := 1;
         Reps : W_Clone_Substitution_Array :=
           (1 .. Subst_Length (Assoc, Labs) => <>);
      begin
         Current := 1;
         CurAssoc := First (Assoc);
         CurLabs := First (Labs);
         while Present (CurAssoc) loop
            declare
               Param : constant Node_Id :=
                 Explicit_Generic_Actual_Parameter (CurAssoc);
               Formal : constant Node_Id :=
                 Get_Assoc_From_Param (CurAssoc, CurLabs);
               Actual : constant W_Identifier_Id :=
                 +To_Why_Id (Entity (Param), Domain => EW_Term);
               Actual_Type : constant W_Primitive_Type_Id :=
                 +Why_Logic_Type_Of_Ada_Type (Entity (Param));
               Theory_Name : constant String :=
                  Clone_Name & "__" & Short_Name (Formal);
               TFile : Why_File :=
                 Why_Files (Dispatch_Entity (Package_Entity));
            begin
               case Ekind (Formal) is
                  when Type_Kind =>
                     if Ekind (Formal) in Integer_Kind then
                        Reps (Current) := New_Clone_Substitution
                          (Kind      => EW_Type_Subst,
                           Orig_Name => New_Identifier
                             (Name => Short_Name (Formal)),
                           Image     => Actual);
                        Reps (Current + 1) := New_Clone_Substitution
                          (Kind      => EW_Function,
                           Orig_Name => New_Identifier
                             (Name => Short_Name (Formal) &  "__" &
                                To_String (WNE_To_Int)),
                           Image     => New_Identifier
                             (Context => Full_Name (Entity (Param)),
                              Name => To_String (WNE_To_Int)));
                        Reps (Current + 2) := New_Clone_Substitution
                          (Kind      => EW_Function,
                           Orig_Name => New_Identifier
                             (Name => Short_Name (Formal) &  "__" &
                                To_String (WNE_Of_Int)),
                           Image     => New_Identifier
                             (Context => Full_Name (Entity (Param)),
                              Name => To_String (WNE_Of_Int)));
                        Reps (Current + 3) := New_Clone_Substitution
                          (Kind      => EW_Function,
                           Orig_Name => New_Identifier
                             (Name => Short_Name (Formal) &  "__" &
                                To_String (WNE_Attr_First)),
                           Image     => New_Identifier
                             (Context => Full_Name (Entity (Param)),
                              Name => To_String (WNE_Attr_First)));
                        Reps (Current + 4) := New_Clone_Substitution
                          (Kind      => EW_Function,
                           Orig_Name => New_Identifier
                             (Name => Short_Name (Formal) &  "__" &
                                To_String (WNE_Attr_Last)),
                           Image     => New_Identifier
                             (Context => Full_Name (Entity (Param)),
                              Name => To_String (WNE_Attr_Last)));
                        Current := Current + 5;
                     else
                        Reps (Current) := New_Clone_Substitution
                          (Kind      => EW_Type_Subst,
                           Orig_Name => New_Identifier
                             (Name => Short_Name (Formal)),
                           Image     => Actual);
                        Current := Current + 1;
                     end if;
                     Open_Theory
                       (TFile, Theory_Name,
                        Comment => "Formal Parameter");
                     Emit
                       (TFile.Cur_Theory,
                        New_Include_Declaration
                          (T_Name   =>
                           New_Identifier
                             (Name => Capitalize_First
                                (Full_Name (Entity (Param)))),
                           Kind     => EW_Module,
                           Use_Kind => EW_Export));
                     if Short_Name (Formal) /= Short_Name (Entity (Param)) then
                        Emit
                          (TFile.Cur_Theory,
                           New_Type (Name       => New_Identifier
                                     (Name => Short_Name (Formal)),
                                     Definition =>
                                       New_Transparent_Type_Definition
                                         (Domain          => EW_Term,
                                          Type_Definition => Actual_Type)));
                     end if;
                     Close_Theory (TFile, Filter_Entity => Empty);
                  when Subprogram_Kind | Object_Kind | Named_Kind =>
                     Reps (Current) := New_Clone_Substitution
                       (Kind      => EW_Function,
                        Orig_Name => New_Identifier
                          (Name => Short_Name (Formal)),
                        Image     => Actual);
                     Current := Current + 1;
                  when others =>
                     raise Program_Error;
               end case;
            end;
            Next (CurAssoc);
            Next (CurLabs);
         end loop;
         return Reps;
      end Parse_Parameters;

      Decls : constant List_Id :=
        Visible_Declarations (Parent (Package_Entity));
      Clone_Name : constant String :=
        Capitalize_First (Full_Name (Package_Entity));
      Generic_Name : constant String :=
        Full_Name (Generic_Parent (Parent (Package_Entity)));
      Assoc : constant List_Id := Generic_Associations
        (Get_Package_Instantiation_Node (Package_Entity));
      --  use Parent field to reach N_Generic_Package_Declaration
      Labs : constant List_Id := Generic_Formal_Declarations (Parent (Parent
        (Parent (Generic_Parent (Parent (Package_Entity))))));
      TFile : Why_File := Why_Files (Dispatch_Entity (Package_Entity));
   begin
      --  Ada.Text_IO.Put_Line ("--------- + --------");
      Open_Theory (TFile, Clone_Name,
                   Comment => "Clone of " & Generic_Name & ".mlw");

      Emit
        (TFile.Cur_Theory,
         New_Clone_Declaration
           (Origin        =>
              New_Identifier (Name => """" & Generic_Name
                              & """.Main"),
            Clone_Kind    => EW_Export,
            Substitutions => Parse_Parameters (Assoc, Labs, Clone_Name),
            Theory_Kind   => EW_Module));

      Close_Theory (TFile, Filter_Entity => Empty,
                    With_Completion => False,
                    Defined_Entity => Package_Entity);

      Parse_Declarations (Decls, Clone_Name);
      --  Ada.Text_IO.Put_Line ("--------- - --------");
   end Translate_Container_Package;

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

end Gnat2Why.Decls;
