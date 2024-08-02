------------------------------------------------------------------------------
--                                                                          --
--                         GNAT RUN-TIME COMPONENTS                         --
--                                                                          --
--                 A D A . S T R I N G S . U N B O U N D E D                --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--          Copyright (C) 1992-2024, Free Software Foundation, Inc.         --
--                                                                          --
-- GNAT is free software;  you can  redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.                                     --
--                                                                          --
-- As a special exception under Section 7 of GPL version 3, you are granted --
-- additional permissions described in the GCC Runtime Library Exception,   --
-- version 3.1, as published by the Free Software Foundation.               --
--                                                                          --
-- You should have received a copy of the GNU General Public License and    --
-- a copy of the GCC Runtime Library Exception along with this program;     --
-- see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see    --
-- <http://www.gnu.org/licenses/>.                                          --
--                                                                          --
-- GNAT was originally developed  by the GNAT team at  New York University. --
-- Extensive contributions were provided by Ada Core Technologies Inc.      --
--                                                                          --
------------------------------------------------------------------------------

with Ada; use Ada;
with Ada.Strings.Fixed;
with Ada.Unchecked_Deallocation;
with SPARK.Lemmas.Integer_Arithmetic;

package body Strunb with
  SPARK_Mode
is

   function Sum (Left, Right : Natural) return Natural with Inline,
     Pre => Right <= Natural'Last - Left;
   --  Returns summary of Left and Right, raise Constraint_Error on overflow

   function Mul (Left, Right : Natural) return Natural with Inline,
     Pre => Long_Long_Integer (Left) * Long_Long_Integer (Right) <= Long_Long_Integer (Natural'Last);
   --  Returns multiplication of Left and Right, raise Constraint_Error on
   --  overflow.

   function Saturated_Sum (Left, Right : Natural) return Natural
     with Post => Saturated_Sum'Result >= Left;
   --  Returns summary of Left and Right or Natural'Last on overflow

   function Saturated_Mul (Left, Right : Positive) return Positive
     with Post => Saturated_Mul'Result >= Left;
   --  Returns multiplication of Left and Right or Natural'Last on overflow

   ---------
   -- "&" --
   ---------

   function "&"
     (Left  : Unbounded_String;
      Right : Unbounded_String) return Unbounded_String
   is
      L_Length : constant Natural := Left.Last;
      R_Length : constant Natural := Right.Last;

      Strlast : constant Natural := Sum (L_Length, R_Length);
      subtype Str is Uninit_String (1 .. Strlast);
      Result  : Unbounded_String :=
        (Reference => new Str'(others => <>),
         Last      => Strlast);
   begin
      Result.Reference (1 .. L_Length) :=
        Left.Reference (1 .. Left.Last);

      if L_Length < Natural'Last then
         Result.Reference (L_Length + 1 .. Result.Last) :=
           Right.Reference (1 .. Right.Last);
      end if;

      return Result;
   end "&";

   function "&"
     (Left  : Unbounded_String;
      Right : String) return Unbounded_String
   is
      L_Length : constant Natural := Left.Last;
      Strlast  : constant Natural := Sum (L_Length, Right'Length);
      subtype Str is Uninit_String (1 .. Strlast);
      Result   : Unbounded_String :=
        (Reference => new Str'(others => <>),
         Last      => Strlast);
   begin
      Result.Reference (1 .. L_Length) := Left.Reference (1 .. Left.Last);

      if L_Length < Natural'Last then
         Result.Reference (L_Length + 1 .. Result.Last) :=
           Uninit_String (Right);
      end if;

      return Unbounded_String (Result);
   end "&";

   function "&"
     (Left  : String;
      Right : Unbounded_String) return Unbounded_String
   is
      R_Length : constant Natural := Right.Last;
      Strlast  : constant Natural := Sum (Left'Length, R_Length);
      subtype Str is Uninit_String (1 .. Strlast);
      Result   : Unbounded_String :=
        (Reference => new Str'(others => <>),
         Last      => Strlast);
   begin
      Result.Reference (1 .. Left'Length) := Uninit_String (Left);

      if Left'Length < Natural'Last then
         Result.Reference (Left'Length + 1 .. Result.Last) :=
           Right.Reference (1 .. Right.Last);
      end if;

      return Unbounded_String (Result);
   end "&";

   function "&"
     (Left  : Unbounded_String;
      Right : Character) return Unbounded_String
   is
      Strlast : constant Natural := Sum (Left.Last, 1);
      subtype Str is Uninit_String (1 .. Strlast);
      Result  : Unbounded_String :=
        (Reference => new Str'(others => <>),
         Last      => Strlast);
   begin
      Result.Reference (1 .. Result.Last - 1) :=
        Left.Reference (1 .. Left.Last);
      Result.Reference (Result.Last) := Right;

      return Unbounded_String (Result);
   end "&";

   function "&"
     (Left  : Character;
      Right : Unbounded_String) return Unbounded_String
   is
      Strlast : constant Natural := Sum (Right.Last, 1);
      subtype Str is Uninit_String (1 .. Strlast);
      Result  : Unbounded_String :=
        (Reference => new Str'(others => <>),
         Last      => Strlast);
   begin
      Result.Reference (1) := Left;
      Result.Reference (2 .. Result.Last) :=
        Right.Reference (1 .. Right.Last);
      return Unbounded_String (Result);
   end "&";

   ---------
   -- "*" --
   ---------

   --  Parts of the proof involving manipulations with the modulo operator
   --  are complicated for the prover and can't be done automatically in
   --  the global subprogram. That's why we isolate them in these two ghost
   --  lemmas.

   procedure Lemma_Mod (Right : String; K : Integer; Ptr : Natural) with
     Ghost,
     Pre =>
       Right'Length /= 0
       and then Ptr mod Right'Length = 0
       and then Ptr in 0 .. Natural'Last - Right'Length
       and then K in Ptr .. Ptr + Right'Length - 1,
     Post => K mod Right'Length = K - Ptr;
   --  Lemma_Mod is applied to an index considered in Lemma_Split to prove
   --  that it has the right value modulo Right'Length.

   procedure Lemma_Split (Right, Result : String; Ptr : Natural) with
     Ghost,
     Relaxed_Initialization => Result,
     Pre                    =>
       Right'Length /= 0
	 and then Result'First = 1
	 and then Result'Last >= 0
	 and then Ptr mod Right'Length = 0
	 and then Ptr in 0 .. Result'Last - Right'Length
	 and then Result (Result'First .. Ptr + Right'Length)'Initialized
	 and then Result (Ptr + 1 .. Ptr + Right'Length) = Right,
     Post                   =>
       (for all K in Ptr + 1 .. Ptr + Right'Length =>
	 Result (K) = Right (Right'First + (K - 1) mod Right'Length));
   --  Lemma_Split is used after Result (Ptr + 1 .. Ptr + Right'Length) is
   --  updated to Right and concludes that the characters match for each
   --  index when taken modulo Right'Length, as the considered slice starts
   --  at index 1 modulo Right'Length.

   ---------------
   -- Lemma_Mod --
   ---------------

   procedure Lemma_Mod (Right : String; K : Integer; Ptr : Natural) is null;

   -----------------
   -- Lemma_Split --
   -----------------

   procedure Lemma_Split (Right, Result : String; Ptr : Natural)
   is
   begin
      for K in Ptr + 1 .. Ptr + Right'Length loop
         Lemma_Mod (Right, K - 1, Ptr);
         pragma Loop_Invariant
           (for all J in Ptr + 1 .. K =>
              Result (J) = Right (Right'First + (J - 1) mod Right'Length));
      end loop;
   end Lemma_Split;

   function "*"
     (Left  : Natural;
      Right : Character) return Unbounded_String
   is
      subtype Str is Uninit_String (1 .. Left);
      Result : Unbounded_String :=
        (Reference => new Str'(others => <>),
         Last      => Left);
   begin
      for J in Result.Reference'Range loop
         Result.Reference (J) := Right;
         pragma Loop_Invariant
           (for all K in 1 .. J =>
              Result.Reference (K)'Initialized and then Result.Reference (K) = Right);
      end loop;

      return Result;
   end "*";

   function "*"
     (Left  : Natural;
      Right : String) return Unbounded_String
   is
      Len    : constant Natural := Right'Length;
      K      : Natural;

      Strlast : constant Natural := Mul (Left, Len);
      subtype Str is Uninit_String (1 .. Strlast);
      Result  : Unbounded_String :=
        (Reference => new Str'(others => <>),
         Last      => Strlast);
   begin
      if Len = 0 then
         return Result;
      end if;

      K := 0;
      for J in 1 .. Left loop
         Result.Reference (K + 1 .. K + Len) := Uninit_String (Right);
         Lemma_Split (Right, String (Result.Reference.all), K);
         K := K + Len;
         pragma Loop_Invariant (K = J * Len);
         pragma Loop_Invariant (Result.Reference (1 .. K)'Initialized);
         pragma Loop_Invariant
           (for all KK in 1 .. K =>
              Result.Reference (KK) = Right (Right'First + (KK - 1) mod Len));
      end loop;

      return Result;
   end "*";

   function "*"
     (Left  : Natural;
      Right : Unbounded_String) return Unbounded_String
   is
      Len    : constant Natural := Right.Last;
      K      : Natural;

      Strlast : constant Natural := Mul (Left, Len);
      subtype Str is Uninit_String (1 .. Strlast);
      Result  : Unbounded_String :=
        (Reference => new Str'(others => <>),
         Last      => Strlast);
   begin
      if Len = 0 then
         return Result;
      end if;

      pragma Assert (Left * Len = Result.Reference'Length);

      K := 0;
      for J in 1 .. Left loop
         SPARK.Lemmas.Integer_Arithmetic.Lemma_Mult_Is_Monotonic (J, Left, Len);
         Result.Reference (K + 1 .. K + Len) :=
           Right.Reference (1 .. Right.Last);
         Lemma_Split (To_String (Right), String (Result.Reference.all), K);
         K := K + Len;
         pragma Loop_Invariant (K = J * Len);
         pragma Loop_Invariant (Result.Reference (1 .. K)'Initialized);
         pragma Loop_Invariant
           (for all KK in 1 .. K =>
              Result.Reference (KK) = To_String (Right) (1 + (KK - 1) mod Len));
      end loop;

      return Result;
   end "*";

   ---------
   -- "<" --
   ---------

   function "<"
     (Left  : Unbounded_String;
      Right : Unbounded_String) return Boolean
   is
   begin
      return
        Left.Reference (1 .. Left.Last) < Right.Reference (1 .. Right.Last);
   end "<";

   function "<"
     (Left  : Unbounded_String;
      Right : String) return Boolean
   is
   begin
      return String (Left.Reference (1 .. Left.Last)) < Right;
   end "<";

   function "<"
     (Left  : String;
      Right : Unbounded_String) return Boolean
   is
   begin
      return Left < String (Right.Reference (1 .. Right.Last));
   end "<";

   ----------
   -- "<=" --
   ----------

   function "<="
     (Left  : Unbounded_String;
      Right : Unbounded_String) return Boolean
   is
   begin
      return
        Left.Reference (1 .. Left.Last) <= Right.Reference (1 .. Right.Last);
   end "<=";

   function "<="
     (Left  : Unbounded_String;
      Right : String) return Boolean
   is
   begin
      return String (Left.Reference (1 .. Left.Last)) <= Right;
   end "<=";

   function "<="
     (Left  : String;
      Right : Unbounded_String) return Boolean
   is
   begin
      return Left <= String (Right.Reference (1 .. Right.Last));
   end "<=";

   ---------
   -- "=" --
   ---------

   function "="
     (Left  : Unbounded_String;
      Right : Unbounded_String) return Boolean
   is
   begin
      return
        Left.Reference (1 .. Left.Last) = Right.Reference (1 .. Right.Last);
   end "=";

   function "="
     (Left  : Unbounded_String;
      Right : String) return Boolean
   is
   begin
      return String (Left.Reference (1 .. Left.Last)) = Right;
   end "=";

   function "="
     (Left  : String;
      Right : Unbounded_String) return Boolean
   is
   begin
      return Left = String (Right.Reference (1 .. Right.Last));
   end "=";

   ---------
   -- ">" --
   ---------

   function ">"
     (Left  : Unbounded_String;
      Right : Unbounded_String) return Boolean
   is
   begin
      return
        String (Left.Reference (1 .. Left.Last)) > String (Right.Reference (1 .. Right.Last));
   end ">";

   function ">"
     (Left  : Unbounded_String;
      Right : String) return Boolean
   is
   begin
      return String (Left.Reference (1 .. Left.Last)) > Right;
   end ">";

   function ">"
     (Left  : String;
      Right : Unbounded_String) return Boolean
   is
   begin
      return Left > String (Right.Reference (1 .. Right.Last));
   end ">";

   ----------
   -- ">=" --
   ----------

   function ">="
     (Left  : Unbounded_String;
      Right : Unbounded_String) return Boolean
   is
   begin
      return
        Left.Reference (1 .. Left.Last) >= Right.Reference (1 .. Right.Last);
   end ">=";

   function ">="
     (Left  : Unbounded_String;
      Right : String) return Boolean
   is
   begin
      return String (Left.Reference (1 .. Left.Last)) >= Right;
   end ">=";

   function ">="
     (Left  : String;
      Right : Unbounded_String) return Boolean
   is
   begin
      return Left >= String (Right.Reference (1 .. Right.Last));
   end ">=";

   ------------
   -- Adjust --
   ------------

   procedure Adjust (Object : in out Unbounded_String)
     with SPARK_Mode => Off
   is
   begin
      --  Copy string, except we do not copy the statically allocated null
      --  string since it can never be deallocated. Note that we do not copy
      --  extra string room here to avoid dragging unused allocated memory.

      if Object.Reference /= Null_String_Access then
         Object.Reference := new Uninit_String'(Object.Reference (1 .. Object.Last));
      end if;
   end Adjust;

   ------------
   -- Append --
   ------------

   procedure Append
     (Source   : in out Unbounded_String;
      New_Item : Unbounded_String)
   is
   begin
      Realloc_For_Chunk (Source, New_Item.Last);

      if Source.Last < Natural'Last then
         Source.Reference (Source.Last + 1 .. Source.Last + New_Item.Last) :=
           New_Item.Reference (1 .. New_Item.Last);
      end if;

      Source.Last := Source.Last + New_Item.Last;
   end Append;

   procedure Append
     (Source   : in out Unbounded_String;
      New_Item : String)
   is
   begin
      Realloc_For_Chunk (Source, New_Item'Length);

      if Source.Last < Natural'Last then
         Source.Reference (Source.Last + 1 .. Source.Last + New_Item'Length) :=
           Uninit_String (New_Item);
      end if;

      Source.Last := Source.Last + New_Item'Length;
   end Append;

   procedure Append
     (Source   : in out Unbounded_String;
      New_Item : Character)
   is
   begin
      Realloc_For_Chunk (Source, 1);
      Source.Reference (Source.Last + 1) := New_Item;
      Source.Last := Source.Last + 1;
   end Append;

   -----------
   -- Count --
   -----------

   function Count
     (Source  : Unbounded_String;
      Pattern : String;
      Mapping : Maps.Character_Mapping := Maps.Identity) return Natural
   is
   begin
      return
        Search.Count (String (Source.Reference (1 .. Source.Last)), Pattern, Mapping);
   end Count;

   function Count
     (Source  : Unbounded_String;
      Pattern : String;
      Mapping : Maps.Character_Mapping_Function) return Natural
   is
   begin
      return
        Search.Count (String (Source.Reference (1 .. Source.Last)), Pattern, Mapping);
   end Count;

   function Count
     (Source : Unbounded_String;
      Set    : Maps.Character_Set) return Natural
   is
   begin
      return Search.Count (String (Source.Reference (1 .. Source.Last)), Set);
   end Count;

   ------------
   -- Delete --
   ------------

   function Delete
     (Source  : Unbounded_String;
      From    : Positive;
      Through : Natural) return Unbounded_String
   is
   begin
      return
        To_Unbounded_String
          (Fixed.Delete (String (Source.Reference (1 .. Source.Last)), From, Through));
   end Delete;

   procedure Delete
     (Source  : in out Unbounded_String;
      From    : Positive;
      Through : Natural)
   is
   begin
      if From > Through then
         null;

      elsif From - 1 > Source.Last then
         raise Index_Error;

      else
         declare
            Len : constant Natural :=
              Natural'Min (Source.Last, Through) - From + 1;

         begin
            if Through < Natural'Last then
               Source.Reference (From .. Source.Last - Len) :=
                 Source.Reference (Through + 1 .. Source.Last);
            end if;

            Source.Last := Source.Last - Len;
         end;
      end if;
   end Delete;

   -------------
   -- Element --
   -------------

   function Element
     (Source : Unbounded_String;
      Index  : Positive) return Character
   is
     (if Index <= Source.Last then
         Source.Reference (Index)
      else
         raise Strings.Index_Error);

   --------------
   -- Finalize --
   --------------

   procedure Finalize (Object : in out Unbounded_String)
     with SPARK_Mode => Off
   is
      procedure Deallocate is
         new Ada.Unchecked_Deallocation (Uninit_String, String_Access);

   begin
      --  Note: Don't try to free statically allocated null string

      if Object.Reference /= Null_String_Access then
         declare
            Old : String_Access := Object.Reference;
            --  The original reference cannot be null, so we must create a
            --  copy which will become null when deallocated.
         begin
            Deallocate (Old);
            Object.Reference := Null_Unbounded_String.Reference;
         end;
         Object.Last := 0;
      end if;
   end Finalize;

   ----------------
   -- Find_Token --
   ----------------

   procedure Find_Token
     (Source : Unbounded_String;
      Set    : Maps.Character_Set;
      From   : Positive;
      Test   : Strings.Membership;
      First  : out Positive;
      Last   : out Natural)
   is
   begin
      Search.Find_Token
        (String (Source.Reference (From .. Source.Last)), Set, Test, First, Last);
   end Find_Token;

   procedure Find_Token
     (Source : Unbounded_String;
      Set    : Maps.Character_Set;
      Test   : Strings.Membership;
      First  : out Positive;
      Last   : out Natural)
   is
   begin
      Search.Find_Token
        (String (Source.Reference (1 .. Source.Last)), Set, Test, First, Last);
   end Find_Token;

   ----------
   -- Free --
   ----------

   procedure Free (X : in out String_Access) with SPARK_Mode => Off is
      procedure Deallocate is
         new Ada.Unchecked_Deallocation (Uninit_String, String_Access);

   begin
      --  Note: Do not try to free statically allocated null string

      if X /= Null_Unbounded_String.Reference then
         Deallocate (X);
      end if;
   end Free;

   ----------
   -- Head --
   ----------

   function Head
     (Source : Unbounded_String;
      Count  : Natural;
      Pad    : Character := Space) return Unbounded_String
   is
   begin
      return To_Unbounded_String
        (String (Fixed.Head (String (Source.Reference (1 .. Source.Last)), Count, Pad)));
   end Head;

   procedure Head
     (Source : in out Unbounded_String;
      Count  : Natural;
      Pad    : Character := Space)
   is
      Old_Len : constant Natural := Source.Last;
      Tmp : constant String_Access :=
        new Uninit_String'(Uninit_String (Fixed.Head (String (Source.Reference (1 .. Source.Last)),
                           Count, Pad)));
      Len : constant Natural := Tmp'Length;
      Old : String_Access := Source.Reference;
   begin
      Source := Unbounded_String'(Reference => Tmp, Last => Len);
      Free (Old);
   end Head;

   -----------
   -- Index --
   -----------

   function Index
     (Source  : Unbounded_String;
      Pattern : String;
      Going   : Strings.Direction := Strings.Forward;
      Mapping : Maps.Character_Mapping := Maps.Identity) return Natural
   is
   begin
      return Search.Index
        (String (Source.Reference (1 .. Source.Last)), Pattern, Going, Mapping);
   end Index;

   function Index
     (Source  : Unbounded_String;
      Pattern : String;
      Going   : Direction := Forward;
      Mapping : Maps.Character_Mapping_Function) return Natural
   is
   begin
      return Search.Index
        (String (Source.Reference (1 .. Source.Last)), Pattern, Going, Mapping);
   end Index;

   function Index
     (Source : Unbounded_String;
      Set    : Maps.Character_Set;
      Test   : Strings.Membership := Strings.Inside;
      Going  : Strings.Direction  := Strings.Forward) return Natural
   is
   begin
      return Search.Index
        (String (Source.Reference (1 .. Source.Last)), Set, Test, Going);
   end Index;

   function Index
     (Source  : Unbounded_String;
      Pattern : String;
      From    : Positive;
      Going   : Direction := Forward;
      Mapping : Maps.Character_Mapping := Maps.Identity) return Natural
   is
   begin
      return Search.Index
        (String (Source.Reference (1 .. Source.Last)), Pattern, From, Going, Mapping);
   end Index;

   function Index
     (Source  : Unbounded_String;
      Pattern : String;
      From    : Positive;
      Going   : Direction := Forward;
      Mapping : Maps.Character_Mapping_Function) return Natural
   is
   begin
      return Search.Index
        (String (Source.Reference (1 .. Source.Last)), Pattern, From, Going, Mapping);
   end Index;

   function Index
     (Source  : Unbounded_String;
      Set     : Maps.Character_Set;
      From    : Positive;
      Test    : Membership := Inside;
      Going   : Direction := Forward) return Natural
   is
   begin
      return Search.Index
        (String (Source.Reference (1 .. Source.Last)), Set, From, Test, Going);
   end Index;

   function Index_Non_Blank
     (Source : Unbounded_String;
      Going  : Strings.Direction := Strings.Forward) return Natural
   is
   begin
      return
        Search.Index_Non_Blank
          (String (Source.Reference (1 .. Source.Last)), Going);
   end Index_Non_Blank;

   function Index_Non_Blank
     (Source : Unbounded_String;
      From   : Positive;
      Going  : Direction := Forward) return Natural
   is
   begin
      return
        Search.Index_Non_Blank
          (String (Source.Reference (1 .. Source.Last)), From, Going);
   end Index_Non_Blank;

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize (Object : in out Unbounded_String)
     with SPARK_Mode => Off
   is
   begin
      Object.Reference := Null_Unbounded_String.Reference;
      Object.Last      := 0;
   end Initialize;

   ------------
   -- Insert --
   ------------

   function Insert
     (Source   : Unbounded_String;
      Before   : Positive;
      New_Item : String) return Unbounded_String
   is
   begin
      return To_Unbounded_String
        (String (Fixed.Insert (String (Source.Reference (1 .. Source.Last)), Before, New_Item)));
   end Insert;

   procedure Insert
     (Source   : in out Unbounded_String;
      Before   : Positive;
      New_Item : String)
   is
   begin
      if Before - 1 > Source.Last then
         raise Index_Error;
      end if;

      Realloc_For_Chunk (Source, New_Item'Length);

      if Before <= Source.Last then
         Source.Reference
           (Before + New_Item'Length .. Source.Last + New_Item'Length) :=
             Source.Reference (Before .. Source.Last);
      end if;

      Source.Reference (Before .. Before - 1 + New_Item'Length) := Uninit_String (New_Item);
      Source.Last := Source.Last + New_Item'Length;
   end Insert;

   ------------
   -- Length --
   ------------

   function Length (Source : Unbounded_String) return Natural is
     (Source.Last);

   ---------
   -- Mul --
   ---------

   function Mul (Left, Right : Natural) return Natural is
     (Left * Right);

   ---------------
   -- Overwrite --
   ---------------

   function Overwrite
     (Source   : Unbounded_String;
      Position : Positive;
      New_Item : String) return Unbounded_String
   is
   begin
      return To_Unbounded_String
        (String (Fixed.Overwrite
          (String (Source.Reference (1 .. Source.Last)), Position, New_Item)));
   end Overwrite;

   procedure Overwrite
     (Source    : in out Unbounded_String;
      Position  : Positive;
      New_Item  : String)
   is
      NL : constant Natural := New_Item'Length;
   begin
      if Position - 1 <= Source.Last - NL then
         Source.Reference (Position .. Position - 1 + NL) := Uninit_String (New_Item);
      else
         declare
	    Tmp : constant String_Access := new Uninit_String'
              (Uninit_String (Fixed.Overwrite
                (String (Source.Reference (1 .. Source.Last)), Position, New_Item)));
            Old : String_Access := Source.Reference;
         begin
            Source.Reference := Tmp;
            Source.Last := Source.Reference'Length;
            Free (Old);
         end;
      end if;
   end Overwrite;

   ---------------
   -- Put_Image --
   ---------------

   procedure Put_Image
     (S : in out Ada.Strings.Text_Buffers.Root_Buffer_Type'Class;
      V : Unbounded_String)
     with SPARK_Mode => Off -- attribute Put_Image is not allowed in SPARK
   is
   begin
      String'Put_Image (S, To_String (Unbounded_String (V)));
   end Put_Image;

   -----------------------
   -- Realloc_For_Chunk --
   -----------------------

   procedure Realloc_For_Chunk
     (Source     : in out Unbounded_String;
      Chunk_Size : Natural)
   is
      Growth_Factor : constant := 2;
      --  The growth factor controls how much extra space is allocated when
      --  we have to increase the size of an allocated unbounded string. By
      --  allocating extra space, we avoid the need to reallocate on every
      --  append, particularly important when a string is built up by repeated
      --  append operations of small pieces. This is expressed as a factor so
      --  2 means add 1/2 of the length of the string as growth space.

      Min_Mul_Alloc : constant := Standard'Maximum_Alignment;
      --  Allocation will be done by a multiple of Min_Mul_Alloc This causes
      --  no memory loss as most (all?) malloc implementations are obliged to
      --  align the returned memory on the maximum alignment as malloc does not
      --  know the target alignment.

      S_Length : constant Natural := Source.Reference'Length;

   begin
      if Chunk_Size > S_Length - Source.Last then
         declare
            New_Size : constant Positive :=
              Saturated_Sum
                (Sum (Source.Last, Chunk_Size), S_Length / Growth_Factor);

            New_Rounded_Up_Size : constant Positive :=
              Saturated_Mul
                ((New_Size - 1) / Min_Mul_Alloc + 1, Min_Mul_Alloc);

            subtype Str is Uninit_String (1 .. New_Rounded_Up_Size);
            Tmp : constant String_Access := new Str'(others => <>);
         begin
            Tmp (1 .. Source.Last) := Source.Reference (1 .. Source.Last);

            declare
               Old : String_Access := Source.Reference;
               --  The original reference cannot be null, so we must create a copy
               --  which will become null when deallocated.
            begin
               Free (Old);
            end;

            Source.Reference := Tmp;
         end;
      end if;
   end Realloc_For_Chunk;

   ---------------------
   -- Replace_Element --
   ---------------------

   procedure Replace_Element
     (Source : in out Unbounded_String;
      Index  : Positive;
      By     : Character)
   is
   begin
      if Index <= Source.Last then
         Source.Reference (Index) := By;
      else
         raise Strings.Index_Error;
      end if;
   end Replace_Element;

   -------------------
   -- Replace_Slice --
   -------------------

   function Replace_Slice
     (Source : Unbounded_String;
      Low    : Positive;
      High   : Natural;
      By     : String) return Unbounded_String
   is
   begin
      return To_Unbounded_String
        (String (Fixed.Replace_Slice
           (String (Source.Reference (1 .. Source.Last)), Low, High, By)));
   end Replace_Slice;

   procedure Replace_Slice
     (Source : in out Unbounded_String;
      Low    : Positive;
      High   : Natural;
      By     : String)
   is
      Tmp : constant String_Access := new Uninit_String'
        (Uninit_String (Fixed.Replace_Slice
           (String (Source.Reference (1 .. Source.Last)), Low, High, By)));
      Len : constant Natural := Tmp'Length;
      Old : String_Access := Source.Reference;
   begin
      Source := Unbounded_String'(Reference => Tmp, Last => Len);
      Free (Old);
   end Replace_Slice;

   -------------------
   -- Saturated_Mul --
   -------------------

   function Saturated_Mul (Left, Right : Positive) return Positive is
     (if Long_Long_Integer (Left) * Long_Long_Integer (Right) <=
        Long_Long_Integer (Natural'Last)
      then
         Mul (Left, Right)
      else
         Natural'Last);

   -------------------
   -- Saturated_Sum --
   -------------------

   function Saturated_Sum (Left, Right : Natural) return Natural is
     (if Right <= Natural'Last - Left then
         Sum (Left, Right)
      else
         Natural'Last);

   --------------------------
   -- Set_Unbounded_String --
   --------------------------

   procedure Set_Unbounded_String
     (Target : in out Unbounded_String;
      Source : String)
   is
      Old : String_Access := Target.Reference;
      subtype Str is Uninit_String (1 .. Source'Length);
   begin
      Target :=
        Unbounded_String'(Reference => new Str'(Str (Source)),
                          Last      => Source'Length);
      Free (Old);
   end Set_Unbounded_String;

   -----------
   -- Slice --
   -----------

   function Slice
     (Source : Unbounded_String;
      Low    : Positive;
      High   : Natural) return String
   is
      --  Note: test of High > Length is in accordance with AI95-00128

     (if Low - 1 > Source.Last or else High > Source.Last then
         raise Index_Error
      else
         String (Source.Reference (Low .. High)));

   ---------
   -- Sum --
   ---------

   function Sum (Left, Right : Natural) return Natural is
     (Left + Right);

   ----------
   -- Tail --
   ----------

   function Tail
     (Source : Unbounded_String;
      Count  : Natural;
      Pad    : Character := Space) return Unbounded_String is
   begin
      return To_Unbounded_String
        (String (Fixed.Tail (String (Source.Reference (1 .. Source.Last)), Count, Pad)));
   end Tail;

   procedure Tail
     (Source : in out Unbounded_String;
      Count  : Natural;
      Pad    : Character := Space)
   is
      Tmp : constant String_Access := new Uninit_String'
        (Uninit_String (Fixed.Tail (String (Source.Reference (1 .. Source.Last)), Count, Pad)));
      Len : constant Natural := Tmp'Length;
      Old : String_Access := Source.Reference;
   begin
      Source := Unbounded_String'(Reference => Tmp, Last => Len);
      Free (Old);
   end Tail;

   ---------------
   -- To_String --
   ---------------

   function To_String (Source : Unbounded_String) return String is
     (String (Source.Reference (1 .. Source.Last)));

   -------------------------
   -- To_Unbounded_String --
   -------------------------

   function To_Unbounded_String
     (Source : String) return Unbounded_String
   is
      subtype Str is Uninit_String (1 .. Source'Length);
      Result : Unbounded_String :=
        (Reference => new Str'(others => <>),
         Last      => Source'Length);
   begin
      Result.Reference.all := Uninit_String (Source);

      return Unbounded_String (Result);
   end To_Unbounded_String;

   function To_Unbounded_String
     (Length : Natural) return Unbounded_String
     with SPARK_Mode => Off
   is
      Result : Unbounded_String;

   begin
      --  Do not allocate an empty string: keep the default

      if Length > 0 then
         Result.Last      := Length;
         Result.Reference := new Uninit_String (1 .. Length);
      end if;

      return Result;
   end To_Unbounded_String;

   ---------------
   -- Translate --
   ---------------

   function Translate
     (Source  : Unbounded_String;
      Mapping : Maps.Character_Mapping) return Unbounded_String
   is
   begin
      return To_Unbounded_String
        (String (Fixed.Translate (String (Source.Reference (1 .. Source.Last)), Mapping)));
   end Translate;

   procedure Translate
     (Source  : in out Unbounded_String;
      Mapping : Maps.Character_Mapping)
   is
   begin
      Fixed.Translate (String (Source.Reference (1 .. Source.Last)), Mapping);
   end Translate;

   function Translate
     (Source  : Unbounded_String;
      Mapping : Maps.Character_Mapping_Function) return Unbounded_String
   is
   begin
      return To_Unbounded_String
        (String (Fixed.Translate (String (Source.Reference (1 .. Source.Last)), Mapping)));
   end Translate;

   procedure Translate
     (Source  : in out Unbounded_String;
      Mapping : Maps.Character_Mapping_Function)
   is
   begin
      Fixed.Translate (String (Source.Reference (1 .. Source.Last)), Mapping);
   end Translate;

   ----------
   -- Trim --
   ----------

   function Trim
     (Source : Unbounded_String;
      Side   : Trim_End) return Unbounded_String
   is
   begin
      pragma Assert (Index_Non_Blank (Source, Forward) =
                       Fixed.Index_Non_Blank (String (Source.Reference (1 .. Source.Last)), Forward));
      pragma Assert (Index_Non_Blank (Source, Backward) =
                       Fixed.Index_Non_Blank (String (Source.Reference (1 .. Source.Last)), Backward));
      return To_Unbounded_String
        (Fixed.Trim (String (Source.Reference (1 .. Source.Last)), Side));
   end Trim;

   procedure Trim
     (Source : in out Unbounded_String;
      Side   : Trim_End)
   is
      pragma Assert (Index_Non_Blank (Source, Forward) =
                       Fixed.Index_Non_Blank (String (Source.Reference (1 .. Source.Last)), Forward));
      pragma Assert (Index_Non_Blank (Source, Backward) =
                       Fixed.Index_Non_Blank (String (Source.Reference (1 .. Source.Last)), Backward));
      Tmp : constant String_Access := new Uninit_String'
        (Uninit_String (Fixed.Trim (String (Source.Reference (1 .. Source.Last)), Side)));
      Len : constant Natural := Tmp'Length;
      Old : String_Access := Source.Reference;
   begin
      Source := Unbounded_String'(Reference => Tmp, Last => Len);
      Free (Old);
   end Trim;

   function Trim
     (Source : Unbounded_String;
      Left   : Maps.Character_Set;
      Right  : Maps.Character_Set) return Unbounded_String
   is
   begin
      pragma Assert (Index (Source, Left, Outside, Forward) =
                       Fixed.Index (String (Source.Reference (1 .. Source.Last)), Left, Outside, Forward));
      pragma Assert (Index (Source, Right, Outside, Backward) =
                       Fixed.Index (String (Source.Reference (1 .. Source.Last)), Right, Outside, Backward));
      return To_Unbounded_String
        (String (Fixed.Trim (String (Source.Reference (1 .. Source.Last)), Left, Right)));
   end Trim;

   procedure Trim
     (Source : in out Unbounded_String;
      Left   : Maps.Character_Set;
      Right  : Maps.Character_Set)
   is
      pragma Assert (Index (Source, Left, Outside, Forward) =
                       Fixed.Index (String (Source.Reference (1 .. Source.Last)), Left, Outside, Forward));
      pragma Assert (Index (Source, Right, Outside, Backward) =
                       Fixed.Index (String (Source.Reference (1 .. Source.Last)), Right, Outside, Backward));
      Tmp : constant String_Access := new Uninit_String'
        (Uninit_String (Fixed.Trim (String (Source.Reference (1 .. Source.Last)), Left, Right)));
      Len : constant Natural := Tmp'Length;
      Old : String_Access := Source.Reference;
   begin
      Source := Unbounded_String'(Reference => Tmp, Last => Len);
      Free (Old);
   end Trim;

   ---------------------
   -- Unbounded_Slice --
   ---------------------

   function Unbounded_Slice
     (Source : Unbounded_String;
      Low    : Positive;
      High   : Natural) return Unbounded_String
   is
   begin
      if Low - 1 > Source.Last or else High > Source.Last then
         raise Index_Error;
      else
         return To_Unbounded_String (String (Source.Reference.all (Low .. High)));
      end if;
   end Unbounded_Slice;

   procedure Unbounded_Slice
     (Source : Unbounded_String;
      Target : out Unbounded_String;
      Low    : Positive;
      High   : Natural)
   is
   begin
      if Low - 1 > Source.Last or else High > Source.Last then
         raise Index_Error;
      else
         Target := To_Unbounded_String (String (Source.Reference.all (Low .. High)));
      end if;
   end Unbounded_Slice;

end Strunb;
