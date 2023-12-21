with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Containers.Functional.Multisets;

procedure Main with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   package Int_Multisets is new SPARK.Containers.Functional.Multisets (Integer);
   use Int_Multisets;

   type List_Cell;
   type List is access List_Cell;
   type List_Cell is record
      V : Integer;
      N : List;
   end record;

   function Length (L : access constant List_Cell) return Big_Natural is
     (if L = null then 0 else Length (L.N) + 1)
   with Subprogram_Variant => (Structural => L);

   function Occurrences (L : access constant List_Cell) return Multiset is
     (if L = null then Empty_Multiset else Add (Occurrences (L.N), L.V))
   with Ghost,
     Subprogram_Variant => (Structural => L);

   function "<=" (V : Integer; L : access constant List_Cell) return Boolean is
     (for all W of Occurrences (L) => V <= W)
   with Ghost;

   function "<=" (L : access constant List_Cell; V : Integer) return Boolean is
     (for all W of Occurrences (L) => W <= V)
   with Ghost;

   function Is_Sorted (L : access constant List_Cell) return Boolean is
     (if L = null then True else L.V <= L.N and then Is_Sorted (L.N))
   with Ghost,
     Subprogram_Variant => (Structural => L);

   ---------------
   -- Quicksort --
   ---------------

   procedure Quicksort (L : in out List) with
     Subprogram_Variant => (Decreases => Length (L)),
     Post => Length (L) = Length (L)'Old
     and then Is_Sorted (L)
     and then Occurrences (L) = Occurrences (L)'Old;

   procedure Filter (Source : in out List; V : Integer; Left, Right : out List) with
     Post => Source = null and then Length (Left) + Length (Right) = Length (Source)'Old
     and then Left <= V and then V <= Right
     and then Occurrences (Source)'Old = Sum (Occurrences (Left), Occurrences (Right));

   procedure Append (Left, Right : in out List) with
     Depends => (Left => +Right, Right => null),
     Pre  => Right /= null
     and then Is_Sorted (Left) and then Is_Sorted (Right)
     and then Left <= Right.V,
     Post => Length (Left) = Length (Left)'Old + Length (Right)'Old
     and then Is_Sorted (Left)
     and then Right = null
     and then Occurrences (Left) = Sum (Occurrences (Left)'Old, Occurrences (Right)'Old);

   procedure Filter (Source : in out List; V : Integer; Left, Right : out List) is
      Occ_S : constant Multiset := Occurrences (Source) with Ghost;
   begin
      if Source = null then
         Left := null;
         Right := null;
      else
         Filter (Source.N, V, Left, Right);
         if Source.V <= V then
            Source.N := Left;
            Left := Source;
            pragma Assert (Occ_S = Sum (Occurrences (Left), Occurrences (Right)));
         else
            Source.N := Right;
            Right := Source;
            pragma Assert (Occ_S = Sum (Occurrences (Left), Occurrences (Right)));
         end if;
         Source := null;
      end if;
   end Filter;

   procedure Append (Left, Right : in out List) is
   begin
      if Left = null then
         Left := Right;
      else
         Append (Left.N, Right);
      end if;
      Right := null;
   end Append;

   procedure Quicksort (L : in out List) is
      Left, Right  : List;
      Occ_LN       : Multiset with Ghost;
   begin
      if L /= null then
         Occ_LN := Occurrences (L.N);
         Filter (L.N, L.V, Left, Right);
         pragma Assert
           (Occ_LN = Sum (Occurrences (Left), Occurrences (Right)));
         Quicksort (Left);
         Quicksort (Right);
         L.N := Right;
         Append (Left, L);
         L := Left;
      end if;
   end Quicksort;

   --------------------
   -- Insertion Sort --
   --------------------

   procedure Insertsort (L : in out List) with
     Subprogram_Variant => (Decreases => Length (L)),
     Post => Length (L) = Length (L)'Old
     and then Is_Sorted (L)
     and then Occurrences (L) = Occurrences (L)'Old;

   procedure Insert (V : in out List; L : in out List) with
     Depends => (L => +V, V => null),
     Pre  => V /= null and then V.N = null and then Is_Sorted (L),
     Post => Occurrences (L) = Add (Occurrences (L)'Old, V.V'Old)
     and Length (L) = Length (L)'Old + 1 and Is_Sorted (L) and V = null;

   procedure Insert (V : in out List; L : in out List) is
      V_V   : constant Integer := V.V with Ghost;
      Occ_L : constant Multiset := Occurrences (L) with Ghost;
   begin
      if L = null then
         L := V;
      elsif V.V <= L.V then
         V.N := L;
         L := V;
      else
         Insert (V, L.N);
         pragma Assert (Occurrences (L) = Add (Occ_L, V_V));
      end if;
      V := null;
   end Insert;

   procedure Insertsort (L : in out List) is
      N : List;
   begin
      if L /= null then
         Insertsort (L.N);
         N := L.N;
         L.N := null;
         Insert (L, N);
         L := N;
      end if;
   end Insertsort;

   ----------------
   -- Merge Sort --
   ----------------

   procedure Mergesort (L : in out List) with
     Subprogram_Variant => (Decreases => Length (L)),
     Post => Length (L) = Length (L)'Old
     and then Is_Sorted (L)
     and then Occurrences (L) = Occurrences (L)'Old;

   procedure Split (Source : in out List; N : Big_Natural; Left, Right : out List) with
     Depends => ((Left, Right) => (Source, N), Source => null),
     Pre  => N <= Length (Source),
     Post => Source = null and then Length (Left) + Length (Right) = Length (Source)'Old
     and then Length (Left) = N
     and then Occurrences (Source)'Old = Sum (Occurrences (Left), Occurrences (Right));

   procedure Merge (Left, Right : in out List)  with
     Depends => (Left => +Right, Right => null),
     Pre  => Is_Sorted (Left) and then Is_Sorted (Right),
     Post => Length (Left) = Length (Left)'Old + Length (Right)'Old
     and then Is_Sorted (Left) and then Right = null
     and then Occurrences (Left) = Sum (Occurrences (Left)'Old, Occurrences (Right)'Old);

   procedure Split (Source : in out List; N : Big_Natural; Left, Right : out List) is
   begin
      if N = 0 then
         Left := null;
         Right := Source;
      else
         Split (Source.N, N - 1, Left, Right);
         Source.N := Left;
         Left := Source;
      end if;
      Source := null;
   end Split;

   procedure Merge (Left, Right : in out List) is
      Occ_L : constant Multiset := Occurrences (Left) with Ghost;
      Occ_R : constant Multiset := Occurrences (Right) with Ghost;
   begin
      if Right = null then
         null;
      elsif Left = null then
         Left := Right;
      elsif Left.V <= Right.V then
         Merge (Left.N, Right);
         pragma Assert (Is_Sorted (Left));
         pragma Assert (Occurrences (Left) = Sum (Occ_L, Occ_R));
      else
         Merge (Left, Right.N);
         Right.N := Left;
         Left := Right;
         pragma Assert (Is_Sorted (Left));
         pragma Assert (Occurrences (Left) = Sum (Occ_L, Occ_R));
      end if;
      Right := null;
   end Merge;

   procedure Mergesort (L : in out List) is
      Left, Right  : List;
   begin
      if Length (L) > 1 then
         Split (L, Length (L) / 2, Left, Right);
         Mergesort (Left);
         Mergesort (Right);
         Merge (Left, Right);
         L := Left;
      end if;
   end Mergesort;

begin
   null;
end Main;
