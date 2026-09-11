pragma Extensions_Allowed (On);
--  Auto_Reclaimed_Handles expose the Finalizable aspect through their
--  instantiation, so a client has to enable extensions itself.

with SPARK.Pointers.Auto_Reclaimed.Immutable;
with SPARK.Pointers.Poisoned.Pointers;
with SPARK.Pointers.Handles.Owning_Handles;
with SPARK.Pointers.Handles.Auto_Reclaimed_Handles;

--  Handles give an abstract, one-word view of a pointer, which is what makes
--  a recursive data structure expressible: the cell type mentions a Handle
--  rather than a pointer to itself. Two flavours are exercised here, the two
--  that the two example_recursive tests do not cover:
--  Auto_Reclaimed_Handles, where reclamation is automatic, and
--  Owning_Handles, where the user reclaims.

procedure Test_Handles with SPARK_Mode is

   ---------------------------------------------------------------
   --  A shared immutable list: reclamation is automatic, so the --
   --  handle flavour is Auto_Reclaimed_Handles.                 --
   ---------------------------------------------------------------

   package Shared_Handles is new
     SPARK.Pointers.Handles.Auto_Reclaimed_Handles.Without_Weak_Handles;

   type S_Cell is record
      V : Natural;
      N : Shared_Handles.Handle;
   end record;

   package Shared_Cells is new SPARK.Pointers.Auto_Reclaimed.Immutable (S_Cell);
   package Shared_Ops is new Shared_Cells.Handle_Operations (Shared_Handles);

   function Id (C : S_Cell) return S_Cell is (C);
   function Create_Cell is new Shared_Cells.Create (S_Cell, Id);

   ------------------------------------------------------------------
   --  A list of owning cells: the user reclaims, so the flavour is --
   --  Owning_Handles.                                             --
   ------------------------------------------------------------------

   package Owned_Handles renames SPARK.Pointers.Handles.Owning_Handles;

   type O_Cell is record
      V : Natural := 0;
      N : Owned_Handles.Handle;
   end record;

   function Is_Reclaimed (X : O_Cell) return Boolean
   is (Owned_Handles.Is_Reclaimed (X.N))
   with Ghost => Static;

   package Owned_Cells is new
     SPARK.Pointers.Poisoned.Pointers (O_Cell, Is_Reclaimed);

   --  The tail handle of a leaf is the default one, which is uninitialized
   --  and so already reclaimed: a leaf owes nothing.

   function Leaf (V : Natural) return O_Cell
   with
     Global => null,
     Post   => Is_Reclaimed (Leaf'Result) and then Leaf'Result.V = V
   is
      C : O_Cell;
   begin
      return (V => V, N => C.N);
   end Leaf;

   function Create_Leaf is new Owned_Cells.Create (Natural, Leaf);

   function Create_Leaf_Handle is new
     Owned_Cells.Handle_Operations.Create_Handle (Natural, Create_Leaf);

begin
   Shared_List :
   declare
      use type Shared_Cells.Pointer;

      --  A handle is built by converting a pointer, so an empty tail is the
      --  handle for the null pointer.

      Empty : constant Shared_Handles.Handle :=
        Shared_Ops.To_Handle (Shared_Cells.Null_Pointer);
      One   : constant Shared_Handles.Handle :=
        Shared_Ops.To_Handle (Create_Cell ((V => 1, N => Empty)));
      Two   : constant Shared_Handles.Handle :=
        Shared_Ops.To_Handle (Create_Cell ((V => 2, N => One)));
      --  Two designates a cell whose tail designates the cell One
      --  designates. Nothing is reclaimed by hand: the cells go when the last
      --  handle to them does.
   begin
      pragma Assert (Static => Shared_Ops.Valid_Handle (Empty));
      pragma Assert (Static => Shared_Ops.Valid_Handle (One));
      pragma Assert (Static => Shared_Ops.Valid_Handle (Two));

      --  Reading back through the handle

      declare
         P : constant Shared_Cells.Pointer := Shared_Ops.Of_Handle (Two);
      begin
         pragma Assert (P /= Shared_Cells.Null_Pointer);
         pragma Assert (Shared_Cells.Constant_Reference (P).V = 2);
      end;
   end Shared_List;

   Owned_Default :
   declare
      C : O_Cell;
      --  An owning handle is not default initialized to anything usable, but
      --  it does start out reclaimed, so a cell built from it owes nothing.
   begin
      pragma Assert (Static => Owned_Handles.Is_Uninitialized (C.N));
      pragma Assert (Static => Is_Reclaimed (C));
      pragma Assert
        (Static => Owned_Cells.Is_Reclaimed (Owned_Cells.Null_Pointer));
   end Owned_Default;

   Owned_Cell :
   declare
      use Owned_Cells.Handle_Operations;
      H : aliased Owned_Handles.Handle := Create_Leaf_Handle (7);
   begin
      pragma Assert (Static => Valid_Handle (H));

      --  Reading the cell through the handle
      pragma Assert
        (Owned_Cells.Constant_Reference (Constant_Reference (H).all).V = 7);

      --  Nothing reclaims for the user here, so the cell is released by hand
      --  through the handle. That leaves the handle designating the null
      --  pointer, which is what discharges it at the end of the block.
      declare
         P : constant not null access Owned_Cells.Pointer := Reference (H);
      begin
         Owned_Cells.Reclaim (P.all);
      end;
   end Owned_Cell;
end Test_Handles;
