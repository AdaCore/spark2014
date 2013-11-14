------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       G N A T 2 W H Y . N O D E S                        --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                        Copyright (C) 2012-2013, AdaCore                  --
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

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

with String_Utils;          use String_Utils;

with Csets;                 use Csets;
with Lib;                   use Lib;
with Nlists;                use Nlists;
with Pprint;                use Pprint;
with Sem_Util;              use Sem_Util;
with Snames;                use Snames;
with Stringt;               use Stringt;
with Urealp;                use Urealp;

with SPARK_Definition;      use SPARK_Definition;
with SPARK_Util;            use SPARK_Util;

with Why.Gen.Names;         use Why.Gen.Names;
with Why.Sinfo;             use Why.Sinfo;

package body Gnat2Why.Nodes is

   function Is_Main_Cunit (N : Node_Id) return Boolean is
     (Get_Cunit_Unit_Number (Parent (N)) = Main_Unit);

   function Is_Spec_Unit_Of_Main_Unit (N : Node_Id) return Boolean is
     (Present (Corresponding_Body (N))
       and then Is_Main_Cunit
        (Unit (Enclosing_Comp_Unit_Node (Corresponding_Body (N)))));

   Why3_Keywords : String_Utils.String_Sets.Set;

   ------------------
   -- Add_To_Graph --
   ------------------

   procedure Add_To_Graph (Map : in out Node_Graphs.Map; From, To : Node_Id) is

      procedure Add_To_Set (Ignored : Node_Id; Set : in out Node_Sets.Set);
      --  Add entity To to set Set

      ----------------
      -- Add_To_Set --
      ----------------

      procedure Add_To_Set (Ignored : Node_Id; Set : in out Node_Sets.Set)
      is
         pragma Unreferenced (Ignored);
      begin
         Set.Include (To);
      end Add_To_Set;

   --  Start of processing for Add_To_Graph

   begin
      if Map.Contains (From) then
         Map.Update_Element (Map.Find (From), Add_To_Set'Access);
      else
         declare
            S : Node_Sets.Set;
         begin
            S.Include (To);
            Map.Insert (From, S);
         end;
      end if;
   end Add_To_Graph;

   ------------------------
   -- Avoid_Why3_Keyword --
   ------------------------

   function Avoid_Why3_Keyword (S : String) return String is
      S_Copy : String := S;
   begin
      Lower_Case_First (S_Copy);
      if Why3_Keywords.Contains (S_Copy) then
         return S_Copy & "__";
      else
         return S_Copy;
      end if;
   end Avoid_Why3_Keyword;

   --------------------
   -- Body_File_Name --
   --------------------

   function Body_File_Name (N : Node_Id) return String is
      CU       : Node_Id := Enclosing_Comp_Unit_Node (N);
      Switch   : Boolean := False;
   begin
      case Nkind (Unit (CU)) is
         when N_Package_Body    |
              N_Subprogram_Body |
              N_Subunit         =>
            null;
         when others =>
            Switch := True;
      end case;
      if Switch and then Present (Library_Unit (CU)) then
         CU := Library_Unit (CU);
      end if;
      return File_Name (Sloc (CU));
   end Body_File_Name;

   -----------------------------------
   -- Body_File_Name_Without_Suffix --
   -----------------------------------

   function Body_File_Name_Without_Suffix (N : Node_Id) return String is
      (File_Name_Without_Suffix (Body_File_Name (N)));

   ---------------
   -- Full_Name --
   ---------------

   function Full_Name (N : Entity_Id) return String is
   begin
      --  In special cases, return a fixed name. These cases should match those
      --  for which Full_Name_Is_Not_Unique_Name returns True.

      if Full_Name_Is_Not_Unique_Name (N) then
         if Is_Standard_Boolean_Type (N) then
            return "bool";
         elsif N = Universal_Fixed then
            return "real";
         else
            raise Program_Error;
         end if;

      --  In the general case, return a name based on the Unique_Name

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

   ----------------------------------
   -- Full_Name_Is_Not_Unique_Name --
   ----------------------------------

   function Full_Name_Is_Not_Unique_Name (N : Entity_Id) return Boolean is
   begin
      return Is_Standard_Boolean_Type (N) or else N = Universal_Fixed;
   end Full_Name_Is_Not_Unique_Name;

   -----------------------
   -- Get_Graph_Closure --
   -----------------------

   function Get_Graph_Closure
     (Map  : Node_Graphs.Map;
      From : Node_Sets.Set) return Node_Sets.Set
   is
      use Node_Sets;
      Result   : Set;
      Work_Set : Set;
      First    : Cursor;
      Cur_Node : Node_Id;

      procedure Update_Work_Set (Ignored : Node_Id; New_Set : Set);
      --  Update sets Result and Work_Set by adding those nodes from New_Set
      --  that have not been encountered yet.

      ---------------------
      -- Update_Work_Set --
      ---------------------

      procedure Update_Work_Set (Ignored : Node_Id; New_Set : Set) is
         pragma Unreferenced (Ignored);
      begin
         for N of New_Set loop
            if not Result.Contains (N) then
               Result.Include (N);
               Work_Set.Include (N);
            end if;
         end loop;
      end Update_Work_Set;

   begin
      Work_Set := From;
      Result := From;

      while not Work_Set.Is_Empty loop
         First := Work_Set.First;
         Cur_Node := Element (First);
         Work_Set.Delete (First);

         if Map.Contains (Cur_Node) then
            Node_Graphs.Query_Element (Position => Map.Find (Cur_Node),
                                       Process  => Update_Work_Set'Access);
         end if;
      end loop;

      return Result;
   end Get_Graph_Closure;

   function Get_Graph_Closure
     (Map  : Node_Graphs.Map;
      From : Node_Id) return Node_Sets.Set
   is
      use Node_Sets;
      Work_Set : Set;
   begin
      Work_Set.Include (From);
      return Get_Graph_Closure (Map, Work_Set);
   end Get_Graph_Closure;

   -------------------
   -- Get_Low_Bound --
   -------------------

   function Get_Low_Bound (E : Entity_Id) return Node_Id is
   begin
      if Ekind (E) = E_String_Literal_Subtype then
         return String_Literal_Low_Bound (E);
      else
         return Low_Bound (Scalar_Range (E));
      end if;
   end Get_Low_Bound;

   ---------------
   -- Get_Range --
   ---------------

   function Get_Range (N : Node_Id) return Node_Id is
   begin
      case Nkind (N) is
         when N_Range                           |
              N_Real_Range_Specification        |
              N_Signed_Integer_Type_Definition  |
              N_Modular_Type_Definition         |
              N_Floating_Point_Definition       |
              N_Ordinary_Fixed_Point_Definition |
              N_Decimal_Fixed_Point_Definition  =>
            return N;

         when N_Subtype_Indication =>
            return Range_Expression (Constraint (N));

         when N_Identifier | N_Expanded_Name =>
            return Get_Range (Entity (N));

         when N_Defining_Identifier =>
            case Ekind (N) is
               when Scalar_Kind =>
                  return Get_Range (Scalar_Range (N));

               when Object_Kind =>
                  return Get_Range (Scalar_Range (Etype (N)));

               when others =>
                  raise Program_Error;
            end case;

         when others =>
            raise Program_Error;
      end case;
   end Get_Range;

   ----------------------
   -- Has_Precondition --
   ----------------------

   function Has_Precondition (E : Entity_Id) return Boolean is
      PPC      : Node_Id;
   begin
      PPC := Pre_Post_Conditions (Contract (E));
      while Present (PPC) loop
         if Pragma_Name (PPC) = Name_Precondition then
            return True;
         end if;
         PPC := Next_Pragma (PPC);
      end loop;
      return False;
   end Has_Precondition;

   -----------------------
   -- In_Main_Unit_Body --
   -----------------------

   function In_Main_Unit_Body (N : Node_Id) return Boolean is
      CU   : constant Node_Id := Enclosing_Comp_Unit_Node (N);
      Root : Node_Id;

   begin
      if No (CU) then
         return False;
      end if;

      Root := Unit (CU);

      case Nkind (Root) is
         when N_Package_Body    |
              N_Subprogram_Body =>

            return Is_Main_Cunit (Root);

         --  The only way a node in a subunit can be seen is when this subunit
         --  is part of the main unit.

         when N_Subunit =>
            return True;

         when N_Package_Declaration            |
              N_Generic_Package_Declaration    |
              N_Subprogram_Declaration         |
              N_Generic_Subprogram_Declaration =>

            return False;

         when N_Package_Renaming_Declaration           |
              N_Generic_Package_Renaming_Declaration   |
              N_Subprogram_Renaming_Declaration        |
              N_Generic_Function_Renaming_Declaration  |
              N_Generic_Procedure_Renaming_Declaration =>

            return False;

         when others =>
            raise Program_Error;
      end case;
   end In_Main_Unit_Body;

   -----------------------
   -- In_Main_Unit_Spec --
   -----------------------

   function In_Main_Unit_Spec (N : Node_Id) return Boolean is
      CU   : constant Node_Id := Enclosing_Comp_Unit_Node (N);
      Root : Node_Id;

   begin
      if No (CU) then
         return False;
      end if;

      Root := Unit (CU);

      case Nkind (Root) is
         when N_Package_Body    |
              N_Subprogram_Body |
              N_Subunit         =>

            return False;

         when N_Package_Declaration            |
              N_Generic_Package_Declaration    |
              N_Subprogram_Declaration         |
              N_Generic_Subprogram_Declaration =>

            return Is_Main_Cunit (Root)
              or else Is_Spec_Unit_Of_Main_Unit (Root);

         when N_Package_Renaming_Declaration           |
              N_Generic_Package_Renaming_Declaration   |
              N_Subprogram_Renaming_Declaration        |
              N_Generic_Function_Renaming_Declaration  |
              N_Generic_Procedure_Renaming_Declaration =>

            return False;

         when others =>
            raise Program_Error;
      end case;
   end In_Main_Unit_Spec;

   -----------------------
   -- In_Some_Unit_Body --
   -----------------------

   function In_Some_Unit_Body (N : Node_Id) return Boolean is
      CU   : constant Node_Id := Enclosing_Comp_Unit_Node (N);
      Root : Node_Id;

   begin
      if No (CU) then
         return False;
      end if;

      Root := Unit (CU);

      return Nkind (Root) in N_Unit_Body
        or else Nkind (Root) = N_Subunit;
   end In_Some_Unit_Body;

   ------------------------
   -- Is_In_Current_Unit --
   ------------------------

   function Is_In_Current_Unit (N : Node_Id) return Boolean is
      Real_Node : constant Node_Id :=
        (if Is_Itype (N) then Associated_Node_For_Itype (N) else N);
   begin

      --  ??? Should be made more efficient

      return In_Main_Unit_Spec (Real_Node) or else
        In_Main_Unit_Body (Real_Node);
   end Is_In_Current_Unit;

   function Is_Pragma_Assert_And_Cut (N : Node_Id) return Boolean
   is
      Orig : constant Node_Id := Original_Node (N);
   begin
      return
        (Present (Orig) and then
         Nkind (Orig) = N_Pragma and then
         Get_Name_String (Chars (Pragma_Identifier (Orig))) =
           "assert_and_cut");
   end Is_Pragma_Assert_And_Cut;

   ------------------------------
   -- Is_Quantified_Loop_Param --
   ------------------------------

   function Is_Quantified_Loop_Param (E : Entity_Id) return Boolean is
   begin
      return
        (Present (Scope (E)) and then
         Present (Parent (Scope (E))) and then
         Nkind (Parent (Scope (E))) = N_Quantified_Expression);
   end Is_Quantified_Loop_Param;

   ----------------------------
   -- Iterate_Call_Arguments --
   ----------------------------

   procedure Iterate_Call_Arguments (Call : Node_Id)
   is
      Params     : constant List_Id := Parameter_Associations (Call);
      Cur_Formal : Node_Id := First_Entity (Entity (Name (Call)));
      Cur_Actual : Node_Id := First (Params);
      In_Named   : Boolean := False;
   begin
      --  We have to deal with named arguments, but the frontend has
      --  done some work for us. All unnamed arguments come first and
      --  are given as-is, while named arguments are wrapped into a
      --  N_Parameter_Association. The field First_Named_Actual of the
      --  function or procedure call points to the first named argument,
      --  that should be inserted after the last unnamed one. Each
      --  Named Actual then points to a Next_Named_Actual. These
      --  pointers point directly to the actual, but Next_Named_Actual
      --  pointers are attached to the N_Parameter_Association, so to
      --  get the next actual from the current one, we need to follow
      --  the Parent pointer.
      --
      --  The Boolean In_Named states how to obtain the next actual:
      --  either follow the Next pointer, or the Next_Named_Actual of
      --  the parent.
      --  We start by updating the Cur_Actual and In_Named variables for
      --  the first parameter.

      if Nkind (Cur_Actual) = N_Parameter_Association then
         In_Named := True;
         Cur_Actual := First_Named_Actual (Call);
      end if;

      while Present (Cur_Formal) and then Present (Cur_Actual) loop
         Handle_Argument (Cur_Formal, Cur_Actual);
         Cur_Formal := Next_Formal (Cur_Formal);

         if In_Named then
            Cur_Actual := Next_Named_Actual (Parent (Cur_Actual));
         else
            Next (Cur_Actual);

            if Nkind (Cur_Actual) = N_Parameter_Association then
               In_Named := True;
               Cur_Actual := First_Named_Actual (Call);
            end if;
         end if;
      end loop;
   end Iterate_Call_Arguments;

   --------------------
   -- Nth_Index_Type --
   --------------------

   function Nth_Index_Type (E : Entity_Id; Dim : Uint) return Node_Id
   is
      Cur   : Int := 1;
      Index : Node_Id := First_Index (E);
   begin
      if Ekind (E) = E_String_Literal_Subtype then
         return E;
      end if;
      while Cur /= Dim loop
         Cur := Cur + 1;
         Next_Index (Index);
      end loop;
      return Etype (Index);
   end Nth_Index_Type;

   function Nth_Index_Type (E : Entity_Id; Dim : Positive) return Node_Id
   is
   begin
      return Nth_Index_Type (E, UI_From_Int (Int (Dim)));
   end Nth_Index_Type;

   -----------------
   -- Source_Name --
   -----------------

   function Source_Name (E : Entity_Id) return String is
      function Short_Name (E : Entity_Id) return String;

      ----------------
      -- Short_Name --
      ----------------

      function Short_Name (E : Entity_Id) return String is
      begin
         Get_Unqualified_Name_String (Chars (E));
         return Name_Buffer (1 .. Name_Len);
      end Short_Name;

   begin
      if not (Comes_From_Source (E)) then
         return Short_Name (E);
      else
         declare
            Sl   : Source_Ptr := Sloc (E);
            TBuf : constant Source_Buffer_Ptr :=
              Source_Text (Get_Source_File_Index (Sl));
            Buf  : Unbounded_String := Null_Unbounded_String;
         begin
            if TBuf (Sl) = '"' then
               return Short_Name (E);
            end if;
            while Identifier_Char (TBuf (Sl)) loop
               Append (Buf, TBuf (Sl));
               Sl := Sl + 1;
            end loop;
            return To_String (Buf);
         end;
      end if;
   end Source_Name;

   ----------------
   -- Short_Name --
   ----------------

   function Short_Name (E : Entity_Id) return String
   is
   begin
      return Avoid_Why3_Keyword (Get_Name_String (Chars (E)));
   end Short_Name;

   --------------------
   -- Spec_File_Name --
   --------------------

   function Spec_File_Name (N : Node_Id) return String
   is
      CU : Node_Id := Enclosing_Comp_Unit_Node (N);
   begin
      case Nkind (Unit (CU)) is
         when N_Package_Body | N_Subunit =>
            CU := Library_Unit (CU);
         when others =>
            null;
      end case;
      return File_Name (Sloc (CU));
   end Spec_File_Name;

   -----------------------------------
   -- Spec_File_Name_Without_Suffix --
   -----------------------------------

   function Spec_File_Name_Without_Suffix (N : Node_Id) return String is
      (File_Name_Without_Suffix (Spec_File_Name (N)));

   --------------------
   -- String_Of_Node --
   --------------------

   function String_Of_Node (N : Node_Id) return String
   is

      function Real_Image (U : Ureal) return String;
      function String_Image (S : String_Id) return String;
      function Ident_Image (Expr        : Node_Id;
                            Orig_Expr   : Node_Id;
                            Expand_Type : Boolean)
                            return String;

      function Node_To_String is new
        Expression_Image (Real_Image, String_Image, Ident_Image);
      --  The actual printing function

      -----------------
      -- Ident_Image --
      -----------------

      function Ident_Image (Expr        : Node_Id;
                            Orig_Expr   : Node_Id;
                            Expand_Type : Boolean)
                            return String
      is
         pragma Unreferenced (Orig_Expr, Expand_Type);
      begin
         if Nkind (Expr) = N_Defining_Identifier then
            return Source_Name (Expr);
         elsif Present (Entity (Expr)) then
            return Source_Name (Entity (Expr));
         else
            return Get_Name_String (Chars (Expr));
         end if;
      end Ident_Image;

      ----------------
      -- Real_Image --
      ----------------

      function Real_Image (U : Ureal) return String is
      begin
         pragma Unreferenced (U);
         --  ??? still to be done
         return "";
      end Real_Image;

      ------------------
      -- String_Image --
      ------------------

      function String_Image (S : String_Id) return String is
      begin
         Name_Len := 0;
         Add_Char_To_Name_Buffer ('"');
         Add_String_To_Name_Buffer (S);
         Add_Char_To_Name_Buffer ('"');
         return Name_Buffer (1 .. Name_Len);
      end String_Image;

   begin
      return Node_To_String (N, "");
   end String_Of_Node;

   ---------------------------------
   -- Subprogram_Full_Source_Name --
   ---------------------------------

   function Subprogram_Full_Source_Name (E : Entity_Id) return String
   is
      Name : constant String := Source_Name (E);
   begin
      if Has_Fully_Qualified_Name (E)
        or else Scope (E) = Standard_Standard
      then
         return Name;
      else
         return Subprogram_Full_Source_Name (Unique_Entity (Scope (E))) &
           "." & Name;
      end if;
   end Subprogram_Full_Source_Name;

   -------------------
   -- Subp_Location --
   -------------------

   function Subp_Location (E : Entity_Id) return String
   is
      Loc  : constant Source_Ptr :=
        Translate_Location (Sloc (E));
      File : constant String := File_Name (Loc);
      Line : constant Physical_Line_Number :=
        Get_Physical_Line_Number (Loc);
   begin
      return
        "GP_Subp:" & File & ":" & Int_Image (Integer (Line));
   end Subp_Location;

   ------------------
   -- Type_Of_Node --
   ------------------

   function Type_Of_Node (N : Node_Id) return Entity_Id is
      T : Entity_Id;
   begin
      if Nkind (N) in N_Entity then
         if Ekind (N) in Type_Kind then
            T := N;
         else
            T := Etype (N);
         end if;
      elsif Nkind (N) in N_Identifier | N_Expanded_Name then
         T := Etype (Entity (N));
      else
         T := Etype (N);
      end if;

      --  The type of a node is either its most underlying type, or else the
      --  special private type in all other cases, represented in the AST by
      --  its type.

      if Entity_In_SPARK (MUT (T)) then
         return MUT (T);
      else
         return T;
      end if;
   end Type_Of_Node;

   function Type_Of_Node (N : Node_Id) return String
   is
      E : constant Entity_Id := Type_Of_Node (N);
   begin
      if Is_Standard_Boolean_Type (E) then
         return Why_Scalar_Type_Name (EW_Bool);
      elsif E = Universal_Fixed then
         return Why_Scalar_Type_Name (EW_Real);
      else
         return Full_Name (E);
      end if;
   end Type_Of_Node;

begin
   Why3_Keywords.Include ("as");
   Why3_Keywords.Include ("abstract");
   Why3_Keywords.Include ("absurd");
   Why3_Keywords.Include ("any");
   Why3_Keywords.Include ("assert");
   Why3_Keywords.Include ("assume");
   Why3_Keywords.Include ("axiom");
   Why3_Keywords.Include ("begin");
   Why3_Keywords.Include ("bool");
   Why3_Keywords.Include ("check");
   Why3_Keywords.Include ("clone");
   Why3_Keywords.Include ("coinductive");
   Why3_Keywords.Include ("constant");
   Why3_Keywords.Include ("do");
   Why3_Keywords.Include ("done");
   Why3_Keywords.Include ("downto");
   Why3_Keywords.Include ("else");
   Why3_Keywords.Include ("end");
   Why3_Keywords.Include ("epsilon");
   Why3_Keywords.Include ("exception");
   Why3_Keywords.Include ("exists");
   Why3_Keywords.Include ("export");
   Why3_Keywords.Include ("false");
   Why3_Keywords.Include ("for");
   Why3_Keywords.Include ("forall");
   Why3_Keywords.Include ("fun");
   Why3_Keywords.Include ("function");
   Why3_Keywords.Include ("ghost");
   Why3_Keywords.Include ("goal");
   Why3_Keywords.Include ("if");
   Why3_Keywords.Include ("import");
   Why3_Keywords.Include ("in");
   Why3_Keywords.Include ("inductive");
   Why3_Keywords.Include ("int");
   Why3_Keywords.Include ("invariant");
   Why3_Keywords.Include ("lemma");
   Why3_Keywords.Include ("let");
   Why3_Keywords.Include ("loop");
   Why3_Keywords.Include ("match");
   Why3_Keywords.Include ("meta");
   Why3_Keywords.Include ("model");
   Why3_Keywords.Include ("module");
   Why3_Keywords.Include ("mutable");
   Why3_Keywords.Include ("namespace");
   Why3_Keywords.Include ("not");
   Why3_Keywords.Include ("old");
   Why3_Keywords.Include ("predicate");
   Why3_Keywords.Include ("private");
   Why3_Keywords.Include ("prop");
   Why3_Keywords.Include ("private");
   Why3_Keywords.Include ("raise");
   Why3_Keywords.Include ("raises");
   Why3_Keywords.Include ("reads");
   Why3_Keywords.Include ("rec");
   Why3_Keywords.Include ("real");
   Why3_Keywords.Include ("then");
   Why3_Keywords.Include ("theory");
   Why3_Keywords.Include ("to");
   Why3_Keywords.Include ("try");
   Why3_Keywords.Include ("true");
   Why3_Keywords.Include ("type");
   Why3_Keywords.Include ("unit");
   Why3_Keywords.Include ("use");
   Why3_Keywords.Include ("val");
   Why3_Keywords.Include ("variant");
   Why3_Keywords.Include ("while");
   Why3_Keywords.Include ("with");
   Why3_Keywords.Include ("writes");
end Gnat2Why.Nodes;
