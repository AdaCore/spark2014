------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--           F L O W . A N A L Y S I S . A N T I A L I A S I N G            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                Copyright (C) 2013-2020, Altran UK Limited                --
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

with Flow_Classwide;      use Flow_Classwide;
with Flow_Error_Messages; use Flow_Error_Messages;
with Flow_Utility;        use Flow_Utility;
with Nlists;              use Nlists;
with Output;              use Output;
with Sem_Aux;             use Sem_Aux;
with Sem_Eval;            use Sem_Eval;
with Sem_Util;            use Sem_Util;
with Sprint;              use Sprint;
with SPARK_Util;          use SPARK_Util;
with VC_Kinds;            use VC_Kinds;
with Why;

package body Flow.Analysis.Antialiasing is

   Trace_Antialiasing : constant Boolean := False;
   --  Enable this for gratuitous tracing output for aliasing detection

   subtype Computed_Aliasing_Result is Aliasing_Check_Result
     range Impossible .. Definite_Aliasing;

   subtype Non_Obvious_Aliasing_Check_Result is Aliasing_Check_Result
     range No_Aliasing .. Definite_Aliasing;

   package Aliasing_Statuses is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Computed_Aliasing_Result,
      Hash            => Node_Hash,
      Equivalent_Keys => "=");

   Aliasing_Status : Aliasing_Statuses.Map := Aliasing_Statuses.Empty_Map;

   function Check_Ranges (Range_A : Node_Id;
                          Range_B : Node_Id)
                          return Non_Obvious_Aliasing_Check_Result;
   --  Checks two ranges for potential overlap

   function Aliasing (A,        B        : Node_Id;
                      Formal_A, Formal_B : Entity_Id)
                      return Computed_Aliasing_Result
   with Pre => Is_Formal (Formal_A)
               and then (No (Formal_B) or else Is_Formal (Formal_B));
   --  Returns if A and B alias

   function Is_Immutable (F : Entity_Id) return Boolean
   with Pre => Is_Formal (F);
   --  Check if the given formal parameter is immutable, as per the rules
   --  of the SPARK RM section 6.4.2(2).

   function Is_By_Copy_Not_Access (F : Entity_Id) return Boolean
   with Pre => Is_Formal (F) and then Is_Immutable (F);
   --  Check if the given formal immutable parameter cannot possibly alias with
   --  others: it is of a by-copy type that is not an access type.
   --  This implements commmon conditionality from the SPARK RM section 6.4.2
   --  paragraphs (3) and (4).

   procedure Check_Node_Against_Node
     (FA       : in out Flow_Analysis_Graphs;
      A, B     : Node_Or_Entity_Id;
      A_Formal : Entity_Id;
      B_Formal : Entity_Id;
      Status   : out Computed_Aliasing_Result)
   with Pre => Is_Formal (A_Formal)
               and then (No (B_Formal) or else Is_Formal (B_Formal));
   --  Checks the two nodes for aliasing and issues an error message if
   --  appropriate. The formal for B can be Empty, in which case we assume it
   --  is a global.

   procedure Update_Status (Status         : in out Computed_Aliasing_Result;
                            Current_Status : Computed_Aliasing_Result);
   --  Updates the aliasing Status only if the Current_Status is worse (in
   --  terms of the ordering given by the type Computed_Aliasing_Result).

   ------------------
   -- Check_Ranges --
   ------------------

   function Check_Ranges (Range_A : Node_Id;
                          Range_B : Node_Id)
                          return Non_Obvious_Aliasing_Check_Result
   is
      function LT (A, B : Node_Id) return Boolean;
      --  Return true iff A < B

      function GE (A, B : Node_Id) return Boolean;
      --  Return true iff A >= B

      function Empty (A, B : Node_Id) return Boolean;
      --  Return true iff A > B

      function Full (A, B : Node_Id) return Boolean;
      --  Return true iff A <= B

      --------
      -- LT --
      --------

      function LT (A, B : Node_Id) return Boolean is
        (Compile_Time_Compare (A, B, True) = LT);

      --------
      -- GE --
      --------

      function GE (A, B : Node_Id) return Boolean is
        (Compile_Time_Compare (A, B, True) in GE | GT | EQ);

      -----------
      -- Empty --
      -----------

      function Empty (A, B : Node_Id) return Boolean is
        (Compile_Time_Compare (A, B, True) = GT);

      ----------
      -- Full --
      ----------

      function Full (A, B : Node_Id) return Boolean is
        (Compile_Time_Compare (A, B, True) in LT | LE | EQ);

      Range_Expr_A : constant Node_Id := Get_Range (Range_A);
      Range_Expr_B : constant Node_Id := Get_Range (Range_B);

      AL : constant Node_Id := Low_Bound  (Range_Expr_A);
      AH : constant Node_Id := High_Bound (Range_Expr_A);
      BL : constant Node_Id := Low_Bound  (Range_Expr_B);
      BH : constant Node_Id := High_Bound (Range_Expr_B);

   --  Start of processing for Check_Range

   begin
      if Empty (AL, AH)
        or else Empty (BL, BH)
        or else LT (AH, BL)
        or else LT (BH, AL)
      then
         --  We definitely have different, non-overlapping ranges; or at least
         --  one of them is empty.
         return No_Aliasing;

      elsif Full (AL, AH) and then Full (BL, BH) and then
        ((GE (AH, BL) and then GE (BH, AL))
           or else
         (GE (BH, AL) and then GE (AH, BL)))
      then
         --  We definitely have overlapping, non-empty ranges
         return Definite_Aliasing;

      else
         --  We don't know
         return Possible_Aliasing;
      end if;
   end Check_Ranges;

   --------------
   -- Aliasing --
   --------------

   function Aliasing (A,        B        : Node_Id;
                      Formal_A, Formal_B : Entity_Id)
                      return Computed_Aliasing_Result
   is
      --  Expressions are not interesting. Names are, but only some:
      Is_Interesting : constant array (Node_Kind) of Boolean :=
        (
         --  Direct name
         N_Identifier                => True,
         N_Expanded_Name             => True,
         N_Defining_Identifier       => True,

         --  Explicit dereference is now in SPARK
         N_Explicit_Dereference      => True,

         --  Indexed component and slices
         N_Indexed_Component         => True,
         N_Slice                     => True,

         --  Selected components
         N_Selected_Component        => True,

         --  Attribute references (the only interesting one is 'access which is
         --  not in SPARK).

         --  Type conversion
         N_Qualified_Expression      => True,
         N_Type_Conversion           => True,

         --  Function call is boring in SPARK as it can't return access, except
         --  for unchecked conversions.
         N_Unchecked_Type_Conversion => True,

         --  Character literals, qualified expressions are boring

         --  Generalized reference and indexing are suitably expanded

         --  Everything else must be an expression and is thus not interesting

         others                      => False);

      Is_Root : constant array (Node_Kind) of Boolean :=
        (N_Identifier          => True,
         N_Expanded_Name       => True,
         N_Defining_Identifier => True,
         others                => False);

      Is_Conversion : constant array (Node_Kind) of Boolean :=
        (N_Qualified_Expression      => True,
         N_Type_Conversion           => True,
         N_Unchecked_Type_Conversion => True,
         others                      => False);

      function Down_One_Level (N : Node_Id) return Node_Id
      with Pre => Is_Interesting (Nkind (N))
                  and then not Is_Root (Nkind (N));
      --  Goes down the parse tree by one level. For example:
      --     * R.X.Y       ->  R.X
      --     * R.X         ->  R
      --     * A (12)      ->  A
      --     * Wibble (X)  ->  X

      procedure Find_Root (N : in out Node_Id; Depth : out Natural)
      with Pre  => Is_Interesting (Nkind (N)),
           Post => Is_Root (Nkind (N))
                   or else not Is_Interesting (Nkind (N));
      --  Calls Down_One_Level until we find an identifier. For example:
      --    * R.X.Y       ->  R
      --    * A (12)      ->  A
      --    * Wibble (X)  ->  X
      --
      --  The Depth is how many times the Down_One_Level was called; see the
      --  Up_Ignoring_Conversions (which is the opposite of this routine) for
      --  why this parameter is needed.

      function Get_Root_Entity (N : Node_Or_Entity_Id) return Entity_Id
      is (case Nkind (N) is
             when N_Defining_Identifier => N,
             when others => Entity (N))
      with Pre => Is_Root (Nkind (N));
      --  Returns the entity attached to N, which is either an identifier of an
      --  actual or a defining entity of a global.

      procedure Up_Ignoring_Conversions
        (N     : in out Node_Id;
         Depth : in out Natural)
      with Pre  => Is_Interesting (Nkind (N)) and then Depth > 0,
           Post => Is_Interesting (Nkind (N)) and then Depth < Depth'Old;
      --  Goes up the parse tree (calling Parent), but not higher than Depth.
      --  If we find a type conversion of some kind we keep going.
      --
      --  The Depth parameter is needed, because if we are analysing a
      --  procedure call that has been inlined for proof, then the actual might
      --  have been relocated under an object renaming declaration. In this
      --  case, a sequence of calls to Parent will miss the top node of the
      --  actual parameter (luckily, all but the final call to Parent appear
      --  reliable). See comments for Original_Node and Relocate_Node.
      --
      --  ??? Perhaps it would be more reliable to not call Parent at all and
      --  detect aliasing similar to how (a simpler version) is implemented in
      --  the frontend; see Refer_Same_Object for that.

      --------------------
      -- Down_One_Level --
      --------------------

      function Down_One_Level (N : Node_Id) return Node_Id is
      begin
         case Nkind (N) is
            when N_Explicit_Dereference
               | N_Indexed_Component
               | N_Slice
               | N_Selected_Component
            =>
               return Prefix (N);

            when N_Type_Conversion
               | N_Unchecked_Type_Conversion
               | N_Qualified_Expression
            =>
               return Expression (N);

            when others =>
               raise Program_Error;
         end case;
      end Down_One_Level;

      ---------------
      -- Find_Root --
      ---------------

      procedure Find_Root (N : in out Node_Id; Depth : out Natural) is
      begin
         Depth := 0;
         while Is_Interesting (Nkind (N)) and then not Is_Root (Nkind (N)) loop
            N     := Down_One_Level (N);
            Depth := Depth + 1;
         end loop;
      end Find_Root;

      -----------------------------
      -- Up_Ignoring_Conversions --
      -----------------------------

      procedure Up_Ignoring_Conversions
        (N     : in out Node_Id;
         Depth : in out Natural)
      is
      begin
         loop
            N := Parent (N);
            Depth := Depth - 1;
            exit when not Is_Conversion (Nkind (N));
         end loop;
      end Up_Ignoring_Conversions;

      Ptr_A, Ptr_B      : Node_Id;
      Depth_A, Depth_B  : Natural;

      Definitive_Result : Boolean := True;

   --  Start of processing for Aliasing

   begin
      if Trace_Antialiasing then
         Write_Str ("antialiasing: checking ");
         Sprint_Node (A);
         Write_Str (" <--> ");
         Sprint_Node (B);
         Write_Eol;
      end if;

      --  First we check if either of the nodes is interesting as
      --  non-interesting nodes cannot introduce aliasing.

      if not Is_Interesting (Nkind (A)) then
         if Trace_Antialiasing then
            Write_Line ("   -> A is not interesting");
         end if;
         return Impossible;
      elsif not Is_Interesting (Nkind (B)) then
         if Trace_Antialiasing then
            Write_Line ("   -> B is not interesting");
         end if;
         return Impossible;
      end if;

      --  Now check the cases involving immutable formal parameters from the
      --  SPARK RM 6.4.2(3).
      declare
         A_Is_Immutable : constant Boolean := Is_Immutable (Formal_A);
         B_Present_And_Immutable : constant Boolean := Present (Formal_B)
           and then Is_Immutable (Formal_B);
      begin
         if A_Is_Immutable and then B_Present_And_Immutable then
            if Trace_Antialiasing then
               Write_Line
                 ("   -> A and B are both immutable formal parameters");
            end if;
            return Impossible;

         --  Determine if at least one of the corresponding formal
         --  parameters is immutable and a by-copy type that is not
         --  an access type

         elsif A_Is_Immutable and then Is_By_Copy_Not_Access (Formal_A) then
            if Trace_Antialiasing then
               Write_Line ("   -> A does not require aa checking");
            end if;
            return Impossible;
         elsif B_Present_And_Immutable
           and then Is_By_Copy_Not_Access (Formal_B)
         then
            if Trace_Antialiasing then
               Write_Line ("   -> B does not require aa checking");
            end if;
            return Impossible;
         end if;
      end;

      --  Ok, so both nodes might potentially alias. We now need to work out
      --  the root nodes of each expression.

      Ptr_A := A;
      Find_Root (Ptr_A, Depth_A);

      Ptr_B := B;
      Find_Root (Ptr_B, Depth_B);

      if Trace_Antialiasing then
         Write_Str ("   -> root of A: ");
         Sprint_Node (Ptr_A);
         Write_Eol;
         Write_Str ("   -> root of B: ");
         Sprint_Node (Ptr_B);
         Write_Eol;
      end if;

      if not Is_Root (Nkind (Ptr_A)) then
         if Trace_Antialiasing then
            Write_Line ("   -> root of A is not interesting");
         end if;
         return Impossible;
      elsif not Is_Root (Nkind (Ptr_B)) then
         if Trace_Antialiasing then
            Write_Line ("   -> root of B is not interesting");
         end if;
         return Impossible;
      end if;

      --  A quick sanity check. If the root nodes refer to different entities
      --  then we cannot have aliasing.

      if Entity (Ptr_A) /= Get_Root_Entity (Ptr_B) then
         if Trace_Antialiasing then
            Write_Line ("   -> different root entities");
         end if;
         return Impossible;
      end if;

      --  We now know that the root nodes refer to the same entity

      --  From the SPARK RM 6.4.2(1) an object is 'interfering' if it is
      --  unsynchronised or it is synchronised only due to being constant after
      --  elaboration.

      if Is_Synchronized_Object (Entity (Ptr_A))
        and then (Ekind (Entity (Ptr_A)) /= E_Variable
                  or else not Is_Constant_After_Elaboration (Entity (Ptr_A)))
      then
         if Trace_Antialiasing then
            Write_Line ("   -> non-interfering objects");
         end if;
         return Impossible;
      end if;

      --  We now need to walk up the tree and see if we differ somehow.
      --  For example, right now we might have:
      --     * A,              A           --  illegal
      --     * A.X.Y (1 .. J), A.X         --  illegal
      --     * A.X,            A.Y         --  OK
      --     * A (J),          A (K)       --  maybe illegal
      --     * A.X,            Wibble (A)  --  illegal
      --     * A,              Wibble (A)  --  illegal
      --  etc.
      --
      --  Also, we know that Is_Root holds for Ptr_A and Ptr_B, which means
      --  that we are dealing with an identifier and not an unchecked
      --  conversion, etc.

      if Trace_Antialiasing then
         Write_Line ("   -> same root entity");
      end if;

      while Depth_A > 0 and then Depth_B > 0 loop

         --  Go up the tree one level. If we hit an unchecked conversion or
         --  type conversion we 'ignore' it. For example:
         --     * R.X  ->  R.X.Y
         --     * R    ->  Wibble (R).X
         --     * R    ->  Wibble (R)    (if Wibble (R) is the top)

         Up_Ignoring_Conversions (Ptr_A, Depth_A);
         Up_Ignoring_Conversions (Ptr_B, Depth_B);

         pragma Assert (not Is_Root (Nkind (Ptr_A)));
         pragma Assert (not Is_Root (Nkind (Ptr_B)));

         --  Check if we are dealing with any type conversion *now*. If so, we
         --  have aliasing.

         if Is_Conversion (Nkind (Ptr_A)) or else
           Is_Conversion (Nkind (Ptr_B))
         then
            if Trace_Antialiasing then
               Write_Line ("   -> identical tree followed by conversion");
            end if;
            return Definite_Aliasing;
         end if;

         --  We have now gone up one level on each side. We need to check the
         --  two fields.

         if Nkind (Ptr_A) = Nkind (Ptr_B) then

            --  We definitely need to check this. Some possibilities:
            --     R.X         <-->  R.X.Y
            --     R.X         <-->  R.Z
            --     A (5)       <-->  A (J).Wibble
            --     A (1 .. 3)  <-->  A (K .. L)

            if Trace_Antialiasing then
               Write_Str ("   -> checking same structure at ");
               Sprint_Node (Ptr_A);
               Write_Str (" <--> ");
               Sprint_Node (Ptr_B);
               Write_Eol;
            end if;

            case Nkind (Ptr_A) is
               when N_Selected_Component =>
                  if Entity (Selector_Name (Ptr_A)) /=
                     Entity (Selector_Name (Ptr_B))
                  then
                     if Trace_Antialiasing then
                        Write_Line ("   -> selectors differ");
                     end if;
                     return No_Aliasing;
                  end if;

               when N_Indexed_Component =>
                  declare
                     Index_A : Node_Id := First (Expressions (Ptr_A));
                     Index_B : Node_Id := First (Expressions (Ptr_B));
                  begin
                     while Present (Index_A) loop
                        pragma Assert (Present (Index_B));

                        case Compile_Time_Compare (Index_A, Index_B, True) is
                           when LT | GT | NE =>
                              if Trace_Antialiasing then
                                 Write_Str ("   -> index ");
                                 Sprint_Node (Index_A);
                                 Write_Str (" and ");
                                 Sprint_Node (Index_B);
                                 Write_Line (" statically differ");
                              end if;
                              return No_Aliasing;

                           when EQ =>
                              null;

                           when LE | GE | Unknown =>
                              Definitive_Result := False;
                        end case;

                        Next (Index_A);
                        Next (Index_B);
                     end loop;
                  end;

               when N_Slice =>
                  case Check_Ranges (Discrete_Range (Ptr_A),
                                     Discrete_Range (Ptr_B)) is
                     when No_Aliasing =>
                        if Trace_Antialiasing then
                           Write_Str ("   -> slice ");
                           Sprint_Node (Discrete_Range (Ptr_A));
                           Write_Str (" and ");
                           Sprint_Node (Discrete_Range (Ptr_B));
                           Write_Line (" statically distinct");
                        end if;
                        return No_Aliasing;

                     when Definite_Aliasing =>
                        null;

                     when Possible_Aliasing =>
                        Definitive_Result := False;
                  end case;

               when N_Explicit_Dereference =>
                  null;

               when others =>
                  raise Why.Unexpected_Node;
            end case;

         elsif (Nkind (Ptr_A) = N_Slice and then
                  Nkind (Ptr_B) = N_Indexed_Component) or else
           (Nkind (Ptr_A) = N_Indexed_Component and then
              Nkind (Ptr_B) = N_Slice)
         then

            --  We also need to check this. One possibility:
            --     A (1 .. 3)  <-->  A (J)

            --  If the user *really* wants this we can implement it. For now
            --  skip this as its potentially quite hard as we need to sync up
            --  with the other expression.
            --
            --  Consider this: A (4 .. 10) (5 .. 8) (3)

            if Trace_Antialiasing then
               Write_Line
                 ("   -> slice v.s. index is difficult - bailing out");
            end if;

            return Possible_Aliasing;

         else

            --  We have previously established that things might possibly
            --  alias, which means the tree should have been similar enough.
            --  Look for the bug in the above code.

            raise Why.Unexpected_Node;
         end if;

      end loop;

      --  The tree so far was exactly the same, so A and B definitely alias

      if Trace_Antialiasing then
         Write_Line ("   -> identical tree so far, hit end");
         if Definitive_Result then
            Write_Line ("   -> result is definitive");
         end if;
      end if;

      if Definitive_Result then
         return Definite_Aliasing;
      else
         return Possible_Aliasing;
      end if;
   end Aliasing;

   ------------------
   -- Is_Immutable --
   ------------------

   function Is_Immutable (F : Entity_Id) return Boolean is
   begin
      return
        --  It is of mode 'in' and not of an access type
        (Ekind (F) = E_In_Parameter
         and then not Is_Access_Type (Etype (F)))
        or else

      --  ??? The SPARK RM 6.4.2(2) states that anonymous access-to-constant
      --  parameters are immutable. The best we can check for here
      --  appears to be the intersection of 'anonymous access' and
      --  'access constant'.
        (Ekind (F) = E_Anonymous_Access_Type
         and then Is_Access_Constant (Etype (F)));

   end Is_Immutable;

   ---------------------------
   -- Is_By_Copy_Not_Access --
   ---------------------------

   function Is_By_Copy_Not_Access (F : Entity_Id) return Boolean is
   begin
      --  According to SPARK and Ada RMs here we should test for by-copy type
      --  (e.g. using Is_By_Copy_Type). However, it seems better to treat
      --  private types as really private and check if by-copy property can
      --  be deduced from the public declaration only. If not then we are
      --  conservative and assume the worst case, i.e. that the type is
      --  by-reference. See O916-007.

      return Is_Elementary_Type (Etype (F))
        and then not Is_Access_Type (Etype (F));
   end Is_By_Copy_Not_Access;

   -----------------------------
   -- Check_Node_Against_Node --
   -----------------------------

   procedure Check_Node_Against_Node
     (FA       : in out Flow_Analysis_Graphs;
      A, B     : Node_Or_Entity_Id;
      A_Formal : Entity_Id;
      B_Formal : Entity_Id;
      Status   : out Computed_Aliasing_Result)
   is
      Msg    : Unbounded_String := Null_Unbounded_String;
      B_Node : Node_Id;
   begin
      Status := Aliasing (A, B, A_Formal, B_Formal);

      case Status is
         when Impossible =>
            return;

         when Possible_Aliasing
            | Definite_Aliasing
         =>
            null;

         when No_Aliasing =>
            Append (Msg, "non-aliasing of ");
      end case;

      Append (Msg, "formal parameter");
      if Present (B_Formal) then
         Append (Msg, "s & and &");
         B_Node := B_Formal;
      else
         --  ??? maybe have a special message for generated globals
         Append (Msg, " & and global &");
         B_Node := B;
      end if;

      Append
        (Msg,
         (case Status is
             when No_Aliasing       => " proved",
             when Possible_Aliasing => " might be aliased",
             when Definite_Aliasing => " are aliased",
             when Impossible        => raise Program_Error));

      Error_Msg_Flow (FA       => FA,
                      Msg      => To_String (Msg),
                      Severity =>
                        (case Status is
                         when No_Aliasing       => Info_Kind,
                         when Possible_Aliasing => Medium_Check_Kind,
                         when Definite_Aliasing => High_Check_Kind,
                         when Impossible        => raise Program_Error),
                      N        => A,
                      F1       => Direct_Mapping_Id (A_Formal),
                      F2       => Direct_Mapping_Id (B_Node),
                      Tag      => Aliasing,
                      SRM_Ref  => (if Status = No_Aliasing
                                   then ""
                                   else "6.4.2"));
   end Check_Node_Against_Node;

   --------------------------
   -- Check_Procedure_Call --
   --------------------------

   procedure Check_Procedure_Call
     (FA : in out Flow_Analysis_Graphs;
      N  : Node_Id)
   is
      procedure Check_Parameter (Formal : Entity_Id; Actual : Node_Id);
      --  Check parameters against other parameters and globals.

      procedure Check_Aliasing_In_Call is new
        Iterate_Call_Parameters (Check_Parameter);
      --  The general idea here is to make sure none of the globals and
      --  parameters overlap. If we have a procedure with parameters X, Y and
      --  Z and globals A and B, then we check the following:
      --
      --     X v.s. (Y, Z, A, B)
      --     Y v.s. (   Z, A, B)
      --     Z v.s. (      A, B)
      --
      --  In particular we do not check the globals against each other and we
      --  do not check combinations of parameters which we have already seen.
      --  This is implemented by this procedure having the same loop as
      --  Check_Parameter_Against_Parameters_And_Globals and by only checking
      --  parameters once we have seen our parameter we compare against.

      function Visible_Globals (FS : Flow_Id_Sets.Set) return Node_Sets.Set
      with Post => (for all E of Visible_Globals'Result =>
                       Is_Global_Entity (E)
                         or else
                       (Ekind (E) = E_Constant
                        and then not Has_Variable_Input (E)));
      --  Returns the subset of FS that is represented by Entity_Ids, which are
      --  globals except when a constant without variable input wrongly appears
      --  in a user-written contract.

      Writes_Or_Reads : Node_Sets.Set;
      --  Global outputs and in_outs. For aliasing these behave as OUT and
      --  IN_OUT formal parameters, respectively.

      Reads_Only      : Node_Sets.Set;
      --  Global inputs and proof_ins (which for aliasing behave as immutable
      --  IN formal parameters). Note that global access types are never
      --  regarded as purely mode "in" (unlike the similar case for formal
      --  parameters) so are never members of this set.

      Current_Status : Computed_Aliasing_Result;
      Status         : Computed_Aliasing_Result := Impossible;

      ---------------------
      -- Check_Parameter --
      ---------------------

      procedure Check_Parameter (Formal : Entity_Id; Actual : Node_Id) is
         Formal_Is_Immutable : constant Boolean := Is_Immutable (Formal);

         Other_Formal : Entity_Id := Next_Formal (Formal);
         Other_Actual : Node_Id   := Next_Actual (Actual);
         --  Formal/Actual will be checked against formals/actuals that follow
         --  them; this way we check each pair of them exactly once.

      begin
         while Present (Other_Formal) loop
            pragma Assert (Present (Other_Actual));

            Check_Node_Against_Node
              (FA       => FA,
               A        => Actual,
               B        => Other_Actual,
               A_Formal => Formal,
               B_Formal => Other_Formal,
               Status   => Current_Status);

            Update_Status (Status, Current_Status);

            Next_Formal (Other_Formal);
            Next_Actual (Other_Actual);
         end loop;

         pragma Assert (No (Other_Actual));

         --  The rules of SPARK RM 6.4.2(4) are such that:
         --  * If the formal parameter is immutable, there cannot be aliasing
         --    between it and any read-only global.
         if Formal_Is_Immutable then
            if Trace_Antialiasing and then not Reads_Only.Is_Empty then
               Write_Line ("   -> A does not require aa checking against " &
                             "read-only globals");
            end if;
         else
            for G of Reads_Only loop
               Check_Node_Against_Node
                 (FA       => FA,
                  A        => Actual,
                  B        => G,
                  A_Formal => Formal,
                  B_Formal => Empty,
                  Status   => Current_Status);

               Update_Status (Status, Current_Status);
            end loop;
         end if;

         --  * If the formal parameter is an immutable by-copy type that is not
         --  an access type, then there cannot be aliasing between it and any
         --  output or in-out global.
         if Formal_Is_Immutable and then Is_By_Copy_Not_Access (Formal) then
            if Trace_Antialiasing and then not Writes_Or_Reads.Is_Empty then
               Write_Line ("   -> A does not require aa checking against " &
                             "OUT or IN_OUT globals");
            end if;
         else
            for G of Writes_Or_Reads loop
               Check_Node_Against_Node
                 (FA       => FA,
                  A        => Actual,
                  B        => G,
                  A_Formal => Formal,
                  B_Formal => Empty,
                  Status   => Current_Status);

               Update_Status (Status, Current_Status);
            end loop;
         end if;
      end Check_Parameter;

      ---------------------
      -- Visible_Globals --
      ---------------------

      function Visible_Globals (FS : Flow_Id_Sets.Set) return Node_Sets.Set
      is
         Results : Node_Sets.Set;
      begin
         for F of FS loop
            case F.Kind is
               when Direct_Mapping =>
                  Results.Insert (Get_Direct_Mapping_Id (F));

                  --  If we don't have an Entity_Id for a global, then it can't
                  --  be referenced as a parameter.

               when Magic_String =>
                  null;

               when others =>
                  raise Program_Error;
            end case;
         end loop;

         return Results;
      end Visible_Globals;

      --  Local variables

      Globals : Global_Flow_Ids;

      use type Node_Sets.Set;

   --  Start of processing for Check_Procedure_Call

   begin
      Get_Globals (Subprogram => Get_Called_Entity (N),
                   Scope      => FA.B_Scope,
                   Classwide  => Flow_Classwide.Is_Dispatching_Call (N),
                   Globals    => Globals);

      Writes_Or_Reads := Visible_Globals (Globals.Outputs);
      Reads_Only      :=
        (Visible_Globals (Globals.Inputs) - Writes_Or_Reads) or
          Visible_Globals (Globals.Proof_Ins);

      --  Check formal parameters against other parameters and globals

      Check_Aliasing_In_Call (N);

      Aliasing_Status.Insert (N, Status);

      --  ??? Need to check for aliasing between abstract state and computed
      --  globals.

   end Check_Procedure_Call;

   -----------------------------------
   -- Get_Aliasing_Status_For_Proof --
   -----------------------------------

   function Get_Aliasing_Status_For_Proof (N : Node_Id)
                                           return Aliasing_Check_Result
   is
      C : constant Aliasing_Statuses.Cursor := Aliasing_Status.Find (N);
   begin
      return (if Aliasing_Statuses.Has_Element (C)
              then Aliasing_Status (C)
              else Unchecked);
   end Get_Aliasing_Status_For_Proof;

   -------------------
   -- Update_Status --
   -------------------

   procedure Update_Status (Status         : in out Computed_Aliasing_Result;
                            Current_Status : Computed_Aliasing_Result)
   is
   begin
      if Current_Status > Status then
         Status := Current_Status;
      end if;
   end Update_Status;

end Flow.Analysis.Antialiasing;
