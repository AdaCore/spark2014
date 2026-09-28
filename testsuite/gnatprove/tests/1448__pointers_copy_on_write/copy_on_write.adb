with SPARK.Pointers.Explicit_Reclamation.Separate_Memory;

--  A copy-on-write container over
--  SPARK.Pointers.Explicit_Reclamation.Separate_Memory.
--
--  Copying a container is O(1): both containers designate the same cell and
--  the cell's use count goes up. A write splits the sharing -- if anyone else
--  designates the cell, the writer takes a private copy first -- so a copy
--  behaves as if it had been deep all along.

procedure Copy_On_Write with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   subtype Index is Positive range 1 .. 8;
   type Data is array (Index) of Integer;

   type Cell is record
      Count : Positive;
      Value : Data;
   end record;

   function Is_Reclaimed (Unused : Cell) return Boolean is (True)
   with Ghost => Static, Global => null;

   package Ptrs is new
     SPARK.Pointers.Explicit_Reclamation.Separate_Memory (Cell, Is_Reclaimed);
   use Ptrs;
   use Memory_Model;

   function Copy_Cell (C : Cell) return Cell is (C) with Global => null;
   package Ops is new Ptrs.Copy_Operations (Copy_Cell);
   use Ops;

   type Container is record
      P : Pointer;
   end record;

   ---------------------------------------------------------------
   --  The model: a container designates a valid cell, and the   --
   --  cell's Value is the container's value.                    --
   ---------------------------------------------------------------

   function In_Memory (M : Memory_Map; C : Container) return Boolean
   is (In_Memory (M, C.P))
   with Ghost => Static, Global => null;

   function Value (M : Memory_Map; C : Container) return Data
   is (Get (M, C.P).Value)
   with Ghost => Static, Global => null, Pre => In_Memory (M, C);

   function Count (M : Memory_Map; C : Container) return Positive
   is (Get (M, C.P).Count)
   with Ghost => Static, Global => null, Pre => In_Memory (M, C);

   function Shares (A, B : Container) return Boolean
   is (A.P = B.P)
   with Ghost => Static, Global => null;
   --  Whether two containers designate the same cell. Only expressible
   --  because the memory model exposes cell identity, though the memory
   --  itself is not needed to say it.

   -----------------
   --  Operations --
   -----------------

   procedure Create (M : in out Memory_Type; V : Data; C : out Container)
   with
     Global => SPARK.Pointers.Memory_Addresses,
     Post   =>
       (Static =>
          In_Memory (+M, C)
          and then Value (+M, C) = V
          and then Count (+M, C) = 1
          and then Allocates (Memory_Map'(+M)'Old, +M, Only (C.P))
          and then Deallocates (Memory_Map'(+M)'Old, +M, None)
          and then Writes (Memory_Map'(+M)'Old, +M, None));

   procedure Share (M : in out Memory_Type; C : Container; D : out Container)
   with
     Global => null,
     Pre    => (Static => In_Memory (+M, C) and then Count (+M, C) < Positive'Last),
     Post   =>
       (Static =>
          In_Memory (+M, D)
          and then Shares (C, D)
          and then Value (+M, D) = Value (Memory_Map'(+M)'Old, C)
          and then Count (+M, D) = Count (Memory_Map'(+M)'Old, C) + 1
          and then Allocates (Memory_Map'(+M)'Old, +M, None)
          and then Deallocates (Memory_Map'(+M)'Old, +M, None)
          and then Writes (Memory_Map'(+M)'Old, +M, Only (C.P)));
   --  O(1): no data is copied, only the count moves.

   procedure Set
     (M : in out Memory_Type; C : in out Container; I : Index; X : Integer)
   with
     Global => SPARK.Pointers.Memory_Addresses,
     Pre            => (Static => In_Memory (+M, C)),
     Post           =>
       (Static =>
          In_Memory (+M, C)
          and then Value (+M, C) (I) = X
          and then Count (+M, C) = 1
          --  The copy-on-write guarantee: every cell other than the one C
          --  now designates keeps the value it had. A container that was
          --  sharing with C therefore still reads what it read before.
          and then (for all Q in Memory_Map'(+M)'Old =>
                      (if Q /= C.P
                       then Get (+M, Q).Value
                            = Get (Memory_Map'(+M)'Old, Q).Value))
          and then Deallocates (Memory_Map'(+M)'Old, +M, None)),
     Contract_Cases =>
       (Static =>
          (Count (+M, C) = 1 =>
             --  Sole owner: written in place, nothing allocated.
             C.P = C.P'Old
             and Allocates (Memory_Map'(+M)'Old, +M, None)
             and Writes (Memory_Map'(+M)'Old, +M, Only (C.P)),
           others              =>
             --  Shared: C moves to a cell that did not exist before, and the
             --  only cell written is the one it has just left.
             not In_Memory (Memory_Map'(+M)'Old, C.P)
             and Allocates (Memory_Map'(+M)'Old, +M, Only (C.P))
             and Writes (Memory_Map'(+M)'Old, +M, Only (C.P'Old))
             --  and the cell it left has one user fewer
             and Get (+M, C.P'Old).Count
                 = Get (Memory_Map'(+M)'Old, C.P'Old).Count - 1));

   procedure Release (M : in out Memory_Type; C : in out Container)
   with
     Global         => null,
     Depends        => (C => null, M => (C, M)),
     Pre            => (Static => In_Memory (+M, C)),
     Post           => (Static => C.P = Null_Pointer),
     Contract_Cases =>
       (Static =>
          (Count (+M, C) = 1 =>
             --  Last user: the cell goes.
             Deallocates (Memory_Map'(+M)'Old, +M, Only (C.P'Old))
             and Allocates (Memory_Map'(+M)'Old, +M, None)
             and Writes (Memory_Map'(+M)'Old, +M, None),
           others              =>
             Deallocates (Memory_Map'(+M)'Old, +M, None)
             and Allocates (Memory_Map'(+M)'Old, +M, None)
             and Writes (Memory_Map'(+M)'Old, +M, Only (C.P'Old))));

   ---------------
   --  Bodies   --
   ---------------

   procedure Create (M : in out Memory_Type; V : Data; C : out Container) is
   begin
      Create_Copy (M, (Count => 1, Value => V), C.P);
   end Create;

   procedure Share (M : in out Memory_Type; C : Container; D : out Container)
   is
      Acc : constant not null access Cell := Reference (M, C.P);
   begin
      Acc.Count := Acc.Count + 1;
      D := (P => C.P);
   end Share;

   procedure Set
     (M : in out Memory_Type; C : in out Container; I : Index; X : Integer)
   is
      Old : constant Cell := Deref (M, C.P);
   begin
      if Old.Count = 1 then
         declare
            Acc : constant not null access Cell := Reference (M, C.P);
         begin
            Acc.Value (I) := X;
         end;
      else
         declare
            V : Data := Old.Value;
         begin
            V (I) := X;
            declare
               Acc : constant not null access Cell := Reference (M, C.P);
            begin
               Acc.Count := Acc.Count - 1;
            end;
            Create_Copy (M, (Count => 1, Value => V), C.P);
         end;
      end if;
   end Set;

   procedure Release (M : in out Memory_Type; C : in out Container) is
      Old : constant Cell := Deref (M, C.P);
   begin
      if Old.Count = 1 then
         Dealloc (M, C.P);
      else
         declare
            Acc : constant not null access Cell := Reference (M, C.P);
         begin
            Acc.Count := Acc.Count - 1;
         end;
      end if;
      C.P := Null_Pointer;
   end Release;

   -------------------------------------------------------------------
   --  The behaviour the whole design exists for: B is a copy of A  --
   --  that cost nothing, and writing to B leaves A alone.          --
   -------------------------------------------------------------------

   procedure Demo (M : in out Memory_Type)
   with
     Global => SPARK.Pointers.Memory_Addresses,
     Pre    => (Static => Is_Empty (+M)),
     Post   => (Static => Is_Empty (+M))
   is
      A, B : Container;
   begin
      Create (M, (others => 0), A);
      Share (M, A, B);

      --  One cell, two containers, no data copied.
      pragma Assert (Static => Shares (A, B));
      pragma Assert (Static => Count (+M, A) = 2);

      Set (M, B, 1, 99);

      --  The write split them.
      pragma Assert (Static => not Shares (A, B));
      pragma Assert (Static => Value (+M, B) (1) = 99);
      pragma Assert (Static => Value (+M, A) (1) = 0);
      pragma Assert (Static => Count (+M, A) = 1);

      Release (M, A);
      Release (M, B);
   end Demo;

begin
   null;
end Copy_On_Write;
