------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             W H Y - I N T E R                            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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
with AA_Util;             use AA_Util;
with Alfa.Definition;     use Alfa.Definition;
with Einfo;               use Einfo;
with Namet;               use Namet;
with Sem_Util;            use Sem_Util;
with Stand;               use Stand;
with String_Utils;        use String_Utils;
with Constant_Tree;
with Why.Conversions;     use Why.Conversions;
with Why.Atree.Tables;    use Why.Atree.Tables;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Mutators;  use Why.Atree.Mutators;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Expr;        use Why.Gen.Expr;

with Gnat2Why.Decls;      use Gnat2Why.Decls;
with Gnat2Why.Nodes;      use Gnat2Why.Nodes;

package body Why.Inter is

   package Type_Hierarchy is
     new Constant_Tree (EW_Base_Type, EW_Unit);

   function Get_EW_Term_Type (N : Node_Id) return EW_Type;

   procedure Add_With_Clause (T        : W_Theory_Declaration_Id;
                              File     : String;
                              T_Name   : String;
                              Use_Kind : EW_Clone_Type;
                              Th_Type  : EW_Theory_Type := EW_Module);

   package Standard_Imports is

      --  This package serves to trigger the necessary imports on the
      --  _gnatprove_standard file.

      type Standard_Imports_Enum is (SI_Integer,
                                     SI_Float,
                                     SI_Boolean,
                                     SI_Array1,
                                     SI_Array2);

      Imports : array (Standard_Imports_Enum) of Boolean;
      --  This array records whether a standard import is necessary

      procedure Clear;
      --  Reset the import information

      procedure Set_SI (E : Entity_Id);
      --  Depending on the entity, set a required import

      function To_String (E : Standard_Imports_Enum) return String;

   end Standard_Imports;

   package body Standard_Imports is

      procedure Set_SI_Internal (E : Entity_Id);
      --  Internal version of Set_SI doing all the work, with protection
      --  against infinite recursion; is called by Set_SI

      SI_Seen : Node_Sets.Set := Node_Sets.Empty_Set;
      --  "Seen"-Set to infinite recursion of Set_SI_Internal

      -----------
      -- Clear --
      -----------

      procedure Clear is
      begin
         for I in Imports'Range loop
            Imports (I) := False;
         end loop;
      end Clear;

      ---------------------
      -- Set_SI_Internal --
      ---------------------

      procedure Set_SI_Internal (E : Entity_Id) is
      begin
         if not (Nkind (E) in N_Entity) then
            Set_SI_Internal (Etype (E));
            return;
         end if;
         declare
            UE : constant Unique_Entity_Id := Unique (E);
         begin
            if SI_Seen.Contains (+UE) then
               return;
            end if;
            SI_Seen.Include (+UE);
            if Ekind (+UE) in Object_Kind and then
              not Object_Is_In_Alfa (UE) then
               return;
            end if;
            if Ekind (+UE) in Type_Kind and then not Type_Is_In_Alfa (+UE) then
               return;
            end if;
            if Is_Boolean_Type (+UE) then
               Imports (SI_Boolean) := True;
               Imports (SI_Integer) := True;
            else
               case Ekind (+UE) is
               when Discrete_Kind | E_Named_Integer =>
                  Imports (SI_Integer) := True;

               when Float_Kind | Fixed_Point_Kind | E_Named_Real =>
                  Imports (SI_Float) := True;

               when Array_Kind =>
                  Imports (SI_Integer) := True;
                  Set_SI_Internal (Component_Type (+UE));
                  case Number_Dimensions (+UE) is
                  when 1 =>
                     Imports (SI_Array1) := True;
                  when 2 =>
                     Imports (SI_Array2) := True;
                  when others =>
                     raise Program_Error;
                  end case;

               when Private_Kind =>
                  Set_SI_Internal (Underlying_Type (+UE));

               when E_Record_Type =>

                  declare
                     Field            : Node_Id := First_Entity (+UE);
                  begin
                     while Present (Field) loop
                        if Ekind (Field) in Object_Kind then
                           Set_SI_Internal (Etype (Field));
                        end if;
                        Next_Entity (Field);
                     end loop;
                  end;

               when Object_Kind =>
                  Set_SI (Etype (+UE));

               when Subprogram_Kind =>
                  null;

               when others =>
                  raise Program_Error;
               end case;
            end if;
         end;
      end Set_SI_Internal;

      ------------
      -- Set_SI --
      ------------

      procedure Set_SI (E : Entity_Id) is
      begin
         Set_SI_Internal (E);
         SI_Seen.Clear;
      end Set_SI;

      ---------------
      -- To_String --
      ---------------

      function To_String (E : Standard_Imports_Enum) return String is
      begin
         case E is
            when SI_Integer => return "Integer";
            when SI_Float   => return "Floating";
            when SI_Boolean => return "Boolean";
            when SI_Array1  => return "Array__1";
            when SI_Array2  => return "Array__2";
         end case;
      end To_String;

   end Standard_Imports;

   ------------------------
   -- Add_Effect_Imports --
   ------------------------

   procedure Add_Effect_Imports (T : W_Theory_Declaration_Id;
                                 S : Name_Set.Set)
   is
   begin
      for Var of S loop
         if not (Is_Heap_Variable (Var)) then
            declare
               F : constant Entity_Name := File_Of_Entity (Var);
               S : constant String := Capitalize_First (Var.all);
            begin
               Add_With_Clause (T,
                                File_Name_Without_Suffix (F.all) &
                                  Why_File_Suffix (WF_Variables),
                                S,
                                EW_Clone_Default);
            end;
         end if;
      end loop;
   end Add_Effect_Imports;

   procedure Add_Effect_Imports (P : in out Why_File;
                                 S : Name_Set.Set)
   is
   begin
      Add_Effect_Imports (P.Cur_Theory, S);
   end Add_Effect_Imports;

   ---------------------
   -- Add_With_Clause --
   ---------------------

   procedure Add_With_Clause (T        : W_Theory_Declaration_Id;
                              File     : String;
                              T_Name   : String;
                              Use_Kind : EW_Clone_Type;
                              Th_Type  : EW_Theory_Type := EW_Module) is
      File_Ident : constant W_Identifier_Id :=
        (if File = "" then Why_Empty else New_Identifier (Name => File));
   begin
      Theory_Declaration_Append_To_Includes
        (T,
         New_Include_Declaration (File     => File_Ident,
                                  T_Name   => New_Identifier (Name => T_Name),
                                  Use_Kind => Use_Kind,
                                  Kind     => Th_Type));
   end Add_With_Clause;

   procedure Add_With_Clause (P        : in out Why_File;
                              File     : String;
                              T_Name   : String;
                              Use_Kind : EW_Clone_Type;
                              Th_Type  : EW_Theory_Type := EW_Module) is
   begin
      Add_With_Clause (P.Cur_Theory, File, T_Name, Use_Kind, Th_Type);
   end Add_With_Clause;

   procedure Add_With_Clause (P        : in out Why_File;
                              Other    : Why_File;
                              Use_Kind : EW_Clone_Type) is
   begin
      Add_With_Clause (P, Other.Name.all, "Main", Use_Kind);
   end Add_With_Clause;

   -------------------
   -- Base_Why_Type --
   -------------------

   function Base_Why_Type (W : W_Base_Type_Id) return W_Base_Type_Id is
      Kind : constant EW_Type := Get_Base_Type (W);
   begin
      case Kind is
         when EW_Abstract =>
            return Base_Why_Type (Get_Ada_Node (+W));
         when others =>
            return W;
      end case;
   end Base_Why_Type;

   function Base_Why_Type (N : Node_Id) return W_Base_Type_Id is

      --  Get to the unique type, in order to reach the actual base type,
      --  because the private view has another base type (possibly itself).

      E   : constant EW_Type := Get_EW_Term_Type (N);
      Typ : constant Entity_Id := Unique_Entity (Etype (N));
   begin
      case E is
         when EW_Abstract =>
            if Is_Array_Type (Typ) then
               return Why_Types (EW_Array);
            else
               return EW_Abstract (Typ);
            end if;
         when others =>
            return Why_Types (E);
      end case;
   end Base_Why_Type;

   function Base_Why_Type (Left, Right : W_Base_Type_Id) return W_Base_Type_Id
   is
   begin
      return LCA (Base_Why_Type (Left), Base_Why_Type (Right));
   end Base_Why_Type;

   function Base_Why_Type (Left, Right : Node_Id) return W_Base_Type_Id is
   begin
      return Base_Why_Type (Base_Why_Type (Left), Base_Why_Type (Right));
   end Base_Why_Type;

   ------------------
   -- Close_Theory --
   ------------------

   procedure Close_Theory (P             : in out Why_File;
                           Filter_Entity : Entity_Id)
   is

      function File_Base_Name_Of_Entity (E : Entity_Id) return String;
      --  return the base name of the unit in which the entity is
      --  defined

      function Import_Type_Of_Entity (E : Entity_Id) return EW_Clone_Type;
      --  return the import type that is used for such an entity

      function Name_of_Node (N : Node_Id) return String;
      --  return the name which needs to be used to include the Why entity for
      --  that node

      ------------------------------
      -- File_Base_Name_Of_Entity --
      ------------------------------

      function File_Base_Name_Of_Entity (E : Entity_Id) return String is
         U : Node_Id;
      begin
         if Is_In_Standard_Package (E) then
            return Standard_Why_Package_Name;
         end if;
         U := Enclosing_Lib_Unit_Node (E);

         --  Itypes are not attached to the tree, so we go through the
         --  associated node

         if not Present (U) and then Is_Itype (E) then
            U := Enclosing_Lib_Unit_Node (Associated_Node_For_Itype (E));
         end if;

         --  Special handling for entities of subunits, we extract the library
         --  unit

         while Nkind (Unit (U)) = N_Subunit loop
            U := Library_Unit (U);
         end loop;
         return File_Name_Without_Suffix (Sloc (U));
      end File_Base_Name_Of_Entity;

      ---------------------------
      -- Import_Type_Of_Entity --
      ---------------------------

      function Import_Type_Of_Entity (E : Entity_Id) return EW_Clone_Type is
      begin
         if Nkind (E) = N_String_Literal or else Nkind (E) = N_Aggregate then
            return EW_Import;
         end if;
         return EW_Clone_Default;
      end Import_Type_Of_Entity;

      ------------------
      -- Name_of_Node --
      ------------------

      function Name_of_Node (N : Node_Id) return String is
      begin
         if Nkind (N) = N_String_Literal or else Nkind (N) = N_Aggregate then
            return Capitalize_First (New_Temp_Identifier (N));
         end if;
         return Capitalize_First (Full_Name (N));
      end Name_of_Node;

      use Node_Sets;

      S        : constant Node_Sets.Set := Compute_Ada_Nodeset (+P.Cur_Theory);

      Gnatprove_Standard : constant String := "_gnatprove_standard";
   begin

      Standard_Imports.Clear;

      Add_With_Clause (P, Gnatprove_Standard, "Main", EW_Import);

      --  S contains all mentioned Ada entities; for each, we get the
      --  unit where it was defined and add it to the unit set

      if Present (Filter_Entity) then
         Standard_Imports.Set_SI (Filter_Entity);
      end if;

      for N of S loop

         --  Loop parameters may appear, but they do not have a Why
         --  declaration; we skip them here. We also need to protect against
         --  nodes that are not entities, such as string literals

         if N /= Filter_Entity and then
           (if Nkind (N) in N_Entity then Ekind (N) /= E_Loop_Parameter)
           and then
             (if Nkind (N) in N_Entity then Unique_Entity (N) /= Filter_Entity)
         then
            declare
               File_Name   : constant String :=
                 File_Base_Name_Of_Entity (N) &
                 Why_File_Suffix (Dispatch_Entity (N));
               Theory_Name : constant String :=
                 Name_of_Node (N);
               Import      : constant EW_Clone_Type :=
                 Import_Type_Of_Entity (N);
            begin
               Standard_Imports.Set_SI (N);
               if File_Name /= P.Name.all then
                  Add_With_Clause (P, File_Name, Theory_Name, Import);
               else
                  Add_With_Clause (P, "", Theory_Name, Import);
               end if;
            end;
         end if;
      end loop;

      --  We add the dependencies to Gnatprove_Standard theories that may
      --  have been triggered

      declare
         use Standard_Imports;
      begin
         for Index in Imports'Range loop
            if Imports (Index) then
               Add_With_Clause (P,
                                Gnatprove_Standard,
                                To_String (Index),
                                EW_Clone_Default);

               --  Two special cases for infix symbols; these are the only
               --  theories (as opposed to modules) that are used, and the
               --  only ones to be "use import"ed

               if Index = SI_Integer then
                  Add_With_Clause (P,
                                   "int",
                                   "Int",
                                   EW_Import,
                                   EW_Theory);
               elsif Index = SI_Float then
                  Add_With_Clause (P,
                                   "real",
                                   "RealInfix",
                                   EW_Import,
                                   EW_Theory);

               end if;
            end if;
         end loop;
      end;

      File_Append_To_Theories (P.File, +P.Cur_Theory);
      P.Cur_Theory := Why_Empty;
   end Close_Theory;

   ---------------------
   -- Dispatch_Entity --
   ---------------------

   function Dispatch_Entity (E : Entity_Id) return Why_File_Enum
   is
   begin
      if Nkind (E) = N_String_Literal or else Nkind (E) = N_Aggregate then
         return WF_Context_In_Spec;
      end if;
      case Ekind (E) is
         when Subprogram_Kind | E_Subprogram_Body | Named_Kind =>
            if Is_In_Current_Unit (E) and then
              Body_Entities.Contains (Node_Id (Unique (E))) then
               return WF_Context_In_Body;
            else
               return WF_Context_In_Spec;
            end if;

         when Object_Kind =>
            if not Is_Mutable (E) then
               if Is_In_Current_Unit (E) and then
                 Body_Entities.Contains (Node_Id (Unique (E))) then
                  return WF_Context_In_Body;
               else
                  return WF_Context_In_Spec;
               end if;
            else
               return WF_Variables;
            end if;

         when Type_Kind =>
            if Is_In_Current_Unit (E) and then
              Body_Entities.Contains (Node_Id (Unique (E))) then
               return WF_Types_In_Body;
            else
               return WF_Types_In_Spec;
            end if;

         when others =>
            raise Program_Error;

      end case;
   end Dispatch_Entity;

   --------
   -- Eq --
   --------

   function Eq (Left, Right : Entity_Id) return Boolean is
   begin
      if No (Left) or else No (Right) then
         return Left = Right;
      else
         return
           Full_Name (Left) = Full_Name (Right);
      end if;
   end Eq;

   function Eq (Left, Right : W_Base_Type_Id) return Boolean is
      Left_Kind  : constant EW_Type := Get_Base_Type (Left);
      Right_Kind : constant EW_Type := Get_Base_Type (Right);
   begin
      if Left_Kind /= Right_Kind then
         return False;
      end if;

      return Left_Kind /= EW_Abstract
        or else Eq (Get_Ada_Node (+Left), Get_Ada_Node (+Right));
   end Eq;

   -----------------
   -- EW_Abstract --
   -----------------

   function EW_Abstract (N : Node_Id) return W_Base_Type_Id is
   begin
      if N = Standard_Boolean then
         return EW_Bool_Type;
      elsif N = Universal_Fixed then
         return EW_Real_Type;
      else
         return New_Base_Type (Base_Type => EW_Abstract, Ada_Node => N);
      end if;
   end EW_Abstract;

   ---------------
   -- Full_Name --
   ---------------

   function Full_Name (N : Entity_Id) return String is
   begin
      if N = Standard_Boolean then
         return "bool";
      elsif N = Universal_Fixed then
         return "real";
      else
         declare
            S : String := Unique_Name (N);
         begin

            --  In Why3, enumeration literals need to be upper case. Why2
            --  doesn't care, so we enforce upper case here

            if Ekind (N) = E_Enumeration_Literal then
               Capitalize_First (S);
            end if;
            return S;
         end;
      end if;
   end Full_Name;

   -----------------
   -- Get_EW_Type --
   -----------------

   function Get_EW_Type (T : W_Primitive_Type_Id) return EW_Type is
   begin
      if Get_Kind (+T) = W_Base_Type then
         return Get_Base_Type (+T);
      else
         return EW_Abstract;
      end if;
   end Get_EW_Type;

   function Get_EW_Type (T : Node_Id) return EW_Type is
      E : constant EW_Type := Get_EW_Term_Type (T);
   begin
      case E is
         when EW_Scalar =>
            return E;
         when others =>
            return EW_Abstract;
      end case;
   end Get_EW_Type;

   ----------------------
   -- Get_EW_Term_Type --
   ----------------------

   function Get_EW_Term_Type (N : Node_Id) return EW_Type is
      Ty : Node_Id := N;
   begin
      if Nkind (N) /= N_Defining_Identifier
        or else not (Ekind (N) in Type_Kind) then
         Ty := Etype (N);
      end if;

      --  Get to the unique type, to skip private type

      Ty := Unique_Entity (Ty);

      case Ekind (Ty) is
         when Real_Kind =>
            return EW_Real;

         when Discrete_Kind =>
            --  In the case of Standard.Boolean, the base type 'bool' is
            --  used directly. For its subtypes, however, an abstract type
            --  representing a signed int is generated, just like for any
            --  other enumeration subtype.
            --  ??? It would make sense to use a bool-based abstract
            --  subtype in this case, and it should be rather easy to
            --  make this change as soon as theory cloning would work
            --  in Why 3. No point in implementing this improvement
            --  before that, as we have seen no cases where this was a
            --  problem for the prover.

            if Ty = Standard_Boolean then
               return EW_Bool;
            elsif Ty = Universal_Fixed then
               return EW_Real;
            else
               return EW_Int;
            end if;

         when Private_Kind =>
            --  We can only be in this case if Ty is *derived* from a private
            --  type. We go up one step to go the the base type.

            return Get_EW_Term_Type (Etype (Ty));

         when others =>
            return EW_Abstract;
      end case;
   end Get_EW_Term_Type;

   --------------------
   -- Init_Why_Files --
   --------------------

   procedure Init_Why_Files (Prefix : String)
   is
   begin
      for Kind in Why_File_Enum loop
         Why_Files (Kind) :=
           Make_Empty_Why_File (Prefix & Why_File_Suffix (Kind));
      end loop;
   end Init_Why_Files;

   ---------
   -- LCA --
   ---------

   function  LCA (Left, Right : W_Base_Type_Id) return W_Base_Type_Id is
   begin
      if Eq (Left, Right) then
         return Left;
      else
         return Why_Types
           (Type_Hierarchy.LCA
             (Get_Base_Type (Base_Why_Type (Left)),
              Get_Base_Type (Base_Why_Type (Right))));
      end if;
   end LCA;

   -------------------------
   -- Make_Empty_Why_File --
   -------------------------

   function Make_Empty_Why_File (S : String) return Why_File is
   begin
      return
        (Name       => new String'(S),
         File       => New_File,
         Cur_Theory => Why_Empty);
   end Make_Empty_Why_File;

   -----------------
   -- Open_Theory --
   -----------------

   procedure Open_Theory (P    : in out Why_File;
                          Name : String;
                          Kind : EW_Theory_Type := EW_Module) is
      S : constant String := Capitalize_First (Name);
   begin
      P.Cur_Theory :=
        New_Theory_Declaration (Name => New_Identifier (Name => S),
                                Kind => Kind);
   end Open_Theory;

   ---------------
   -- To_Why_Id --
   ---------------

   function To_Why_Id (E      : Entity_Id;
                       Domain : EW_Domain := EW_Prog;
                       Local  : Boolean := False) return W_Identifier_Id
   is
      Suffix : constant String :=
        (case Ekind (E) is
         when Subprogram_Kind | E_Subprogram_Body | Named_Kind =>
           (if Domain = EW_Prog then To_String (WNE_Func)
            else To_String (WNE_Log)),
         when Object_Kind => To_String (WNE_Obj),
         when Type_Kind => To_String (WNE_Type),
         when others => "");
   begin

      --  The component case is sufficiently different to treat it
      --  independently

      if Ekind (E) = E_Component then
         declare
            Field : constant String :=
              "rec__" & Get_Name_String (Chars (E));
            Ada_N : constant Node_Id := Scope (E);
         begin
            if Local then
               return New_Identifier (Ada_Node => Ada_N,
                                      Name     => Field);
            else
               return New_Identifier (Ada_Node => Ada_N,
                                      Name     =>
                                        Capitalize_First (Full_Name (Ada_N)) &
                                        "." & Field);
            end if;
         end;
      elsif Local then
         return New_Identifier (Ada_Node => E, Name => Suffix);
      elsif Suffix = "" then
         return New_Identifier (Ada_Node => E,
                                Name     => Full_Name (E));
      else
         return
           New_Identifier (Ada_Node => E,
                           Name     =>
                             Capitalize_First (Full_Name (E)) & "." & Suffix);
      end if;
   end To_Why_Id;

   function To_Why_Id (Obj : String) return W_Identifier_Id
   is
   begin
      if Obj = Alfa.Name_Of_Heap_Variable then
         return New_Identifier (Name => Alfa.Name_Of_Heap_Variable);
      else
         return New_Identifier (Name => Capitalize_First (Obj) & ".obj");
      end if;
   end To_Why_Id;

   -----------------
   -- To_Why_Type --
   -----------------

   function To_Why_Type (E      : Entity_Id;
                         Local  : Boolean := False) return W_Identifier_Id
   is
   begin
      if Local then
         return New_Identifier (Name => "t");
      else
         return New_Identifier
                 (Ada_Node => E,
                  Name     => Capitalize_First (Full_Name (E)) & ".t");
      end if;
   end To_Why_Type;

   function To_Why_Type (T : String) return W_Identifier_Id
   is
   begin
      if T = Alfa.Name_Of_Heap_Variable then
         return New_Identifier (Name => "__type_of_heap");
      else
         return New_Identifier (Name => Capitalize_First (T) & ".t");
      end if;
   end To_Why_Type;

   --------
   -- Up --
   --------

   function Up (WT : W_Base_Type_Id) return W_Base_Type_Id is
      Kind : constant EW_Type := Get_Base_Type (WT);
   begin
      case Kind is
         when EW_Abstract =>
            return Base_Why_Type (WT);
         when others =>
            return Why_Types (Type_Hierarchy.Up (Kind));
      end case;
   end Up;

   --------
   -- Up --
   --------

   function Up (From, To : W_Base_Type_Id) return W_Base_Type_Id is
   begin
      if Eq (From, To) then
         return From;
      else
         return Up (From);
      end if;
   end Up;

   ---------------------
   -- Why_File_Suffix --
   ---------------------

   function Why_File_Suffix (Kind : Why_File_Enum) return String
   is
   begin
      case Kind is
         when WF_Types_In_Spec =>
            return "__types_in_spec";
         when WF_Types_In_Body =>
            return "__types_in_body";
         when WF_Variables =>
            return "__variables";
         when WF_Context_In_Spec =>
            return "__context_in_spec";
         when WF_Context_In_Body =>
            return "__context_in_body";
         when WF_Main =>
            return "__package";
      end case;
   end Why_File_Suffix;

begin
   Type_Hierarchy.Move_Child (EW_Array, EW_Array);  --  Special self loop
   Type_Hierarchy.Move_Child (EW_Unit, EW_Real);
   Type_Hierarchy.Move_Child (EW_Int, EW_Bool);
   Type_Hierarchy.Move_Child (EW_Real, EW_Int);
   Type_Hierarchy.Freeze;
end Why.Inter;
