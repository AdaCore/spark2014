pragma Extensions_Allowed (On);

with SPARK.Pointers.Auto_Reclaimed.Immutable;
with SPARK.Pointers.Handles.Auto_Reclaimed_Handles;

--  A persistent list over SPARK.Pointers.Auto_Reclaimed.Immutable.
--
--  Persistent in the usual sense: Cons does not modify the list it extends, it
--  returns a new one sharing the whole of it. Two lists built from the same
--  tail share every cell of that tail, and nothing has to be said about it.
--
--  That is the contrast worth reading this example for. In the union-find
--  examples every contract carried Model (Memory), operations stated frame
--  conditions over the whole memory, and Union needed three lemmas to
--  re-establish them. Here there is no memory model at all: a pointer *is* the
--  value it designates, the data is immutable, so nothing an operation does
--  can disturb any list that already exists. Look for a frame condition below
--  and there are none to find.

procedure Persistent_List with SPARK_Mode is

   package Cell_Handles is new
     SPARK.Pointers.Handles.Auto_Reclaimed_Handles.Without_Weak_Handles;

   --  The length is stored in the cell. It cannot go stale, because the cell
   --  is immutable, and it gives Length in O(1) as well as the measure that
   --  makes the recursive definitions below terminate.

   type L_Cell is record
      Value  : Integer;
      Length : Positive;
      Next   : Cell_Handles.Handle;
   end record;

   package Lists is new SPARK.Pointers.Auto_Reclaimed.Immutable (L_Cell);
   use Lists;

   package Ops is new Lists.Handle_Operations (Cell_Handles);
   use Ops;

   function Id (C : L_Cell) return L_Cell is (C) with Global => null;
   function New_Cell is new Lists.Create (L_Cell, Id);

   --------------------------
   --  Reading a list      --
   --------------------------

   function Length (L : Pointer) return Natural
   is (if L = Null_Pointer then 0 else Constant_Reference (L).Length)
   with Global => null;

   function Head (L : Pointer) return Integer
   is (Constant_Reference (L).Value)
   with Global => null, Pre => L /= Null_Pointer;

   --  The stored lengths agree with the structure. Nothing else can break
   --  this once established: the cells are immutable.

   function Valid_List (L : Pointer) return Boolean
   is (L = Null_Pointer
       or else (Valid_Handle (Constant_Reference (L).Next)
                and then Length (Of_Handle (Constant_Reference (L).Next))
                         = Length (L) - 1
                and then Valid_List (Of_Handle (Constant_Reference (L).Next))))
   with
     Ghost              => Static,
     Global             => null,
     Subprogram_Variant => (Decreases => Length (L));

   function Tail (L : Pointer) return Pointer
   is (Of_Handle (Constant_Reference (L).Next))
   with
     Global => null,
     Pre    =>
       (Runtime       => L /= Null_Pointer,
        Static => Valid_List (L));

   --  Two lists share their tail when the handles their head cells store
   --  designate the same cell. Handles have no identity of their own, so the
   --  comparison goes through Extensional_Eq, the equality Handle_Operations
   --  supplies for them.

   function Shares_Tail (L1, L2 : Pointer) return Boolean
   is (Extensional_Eq (Constant_Reference (L1).Next,
                       Constant_Reference (L2).Next))
   with
     Ghost  => Static,
     Global => null,
     Pre    =>
       L1 /= Null_Pointer
       and then L2 /= Null_Pointer
       and then Valid_List (L1)
       and then Valid_List (L2);

   --------------------------
   --  Building a list     --
   --------------------------

   function Empty return Pointer
   is (Null_Pointer)
   with Global => null, Post => Length (Empty'Result) = 0;

   function Cons (X : Integer; L : Pointer) return Pointer
   with
     Global => null,
     Pre    =>
       (Runtime       => Length (L) < Natural'Last,
        Static => Valid_List (L)),
     Post   =>
       (Runtime       =>
          Cons'Result /= Null_Pointer
          and then Length (Cons'Result) = Length (L) + 1
          and then Head (Cons'Result) = X,
        Static =>
          Valid_List (Cons'Result)
          and then Logical_Eq (Tail (Cons'Result), L));

   function Cons (X : Integer; L : Pointer) return Pointer
   is (New_Cell ((Value  => X,
                  Length => Length (L) + 1,
                  Next   => To_Handle (L))));

   --  Walking a list. Nothing is borrowed and nothing is owned, so the walk
   --  is a plain loop over copied pointers.

   function Nth (L : Pointer; N : Positive) return Integer
   with
     Global => null,
     Pre    =>
       (Runtime       => N <= Length (L),
        Static => Valid_List (L));

   --  Append copies the spine of L1 and shares the whole of L2. There is no
   --  contract about L2's cells because there is nothing that could happen to
   --  them.

   function Append (L1, L2 : Pointer) return Pointer
   with
     Global             => null,
     Pre                =>
       (Runtime       => Length (L1) <= Natural'Last - Length (L2),
        Static => Valid_List (L1) and then Valid_List (L2)),
     Post               =>
       (Runtime       =>
          Length (Append'Result) = Length (L1) + Length (L2),
        Static => Valid_List (Append'Result)),
     Subprogram_Variant => (Decreases => Length (L1));

   function Nth (L : Pointer; N : Positive) return Integer is
      C : Pointer := L;
      K : Positive := N;
   begin
      while K > 1 loop
         pragma Loop_Invariant
           (Runtime       => C /= Null_Pointer and then K <= Length (C),
            Static => Valid_List (C));
         pragma Loop_Variant (Decreases => K);
         C := Tail (C);
         K := K - 1;
      end loop;
      return Head (C);
   end Nth;

   function Append (L1, L2 : Pointer) return Pointer
   is (if L1 = Null_Pointer
       then L2
       else Cons (Head (L1), Append (Tail (L1), L2)));

   ------------------------------------------------------------------
   --  The point of the example. Two lists built from the same tail --
   --  share every cell of it, and L survives both untouched. There --
   --  is no frame condition here, and none in Cons: an immutable   --
   --  cell cannot be disturbed, so there is nothing to frame.      --
   ------------------------------------------------------------------

   procedure Demo_Sharing (L : Pointer; X, Y : Integer)
   with
     Global => null,
     Pre    =>
       (Runtime       => Length (L) < Natural'Last,
        Static => Valid_List (L))
   is
      L1 : constant Pointer := Cons (X, L);
      L2 : constant Pointer := Cons (Y, L);
   begin
      pragma Assert (Runtime => Length (L1) = Length (L) + 1);
      pragma Assert (Runtime => Length (L2) = Length (L) + 1);

      --  Both tails are L itself, not a copy of it.
      pragma Assert (Static => Logical_Eq (Tail (L1), L));
      pragma Assert (Static => Logical_Eq (Tail (L2), L));

      --  Not merely equal tails: the two head cells store handles to the one
      --  cell.
      pragma Assert (Static => Shares_Tail (L1, L2));

      --  And L is exactly as it was.
      pragma Assert (Static => Valid_List (L));
   end Demo_Sharing;

   ------------------------------------------------------------------
   --  Congruence. Opaque says nothing about how its result       --
   --  depends on its argument, so the only way to know it agrees --
   --  on two handles is that they are logically equal. That is   --
   --  the half of Extensional_Eq's postcondition a body could    --
   --  not have justified, and it is why the function is          --
   --  imported rather than defined.                              --
   ------------------------------------------------------------------

   function Opaque (H : Cell_Handles.Handle) return Integer
   with Import, Global => null;

   procedure Demo_Congruence (H1, H2 : Cell_Handles.Handle)
   with
     Global => null,
     Pre    =>
       (Static =>
          Valid_Handle (H1)
          and then Valid_Handle (H2)
          and then Extensional_Eq (H1, H2))
   is
   begin
      pragma Assert (Static => Opaque (H1) = Opaque (H2));
   end Demo_Congruence;

begin
   null;
end Persistent_List;
