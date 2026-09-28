pragma Extensions_Allowed (On);

with SPARK.Pointers.Auto_Reclaimed.Global_Memory;
with SPARK.Pointers.Handles.Auto_Reclaimed_Handles;

--  Soundness test. Every check marked FAIL below is a dangerous operation
--  that SPARK has to reject. A check here that starts proving is a hole in
--  the library, not an improvement, so this test is as much a guard as the
--  ones that check things do prove.

procedure Pointers_Soundness with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   package My_Handles is new
     SPARK.Pointers.Handles.Auto_Reclaimed_Handles.With_Weak_Handles;
   use My_Handles;

   type Cell is record
      V : Integer;
   end record;

   package Ptrs is new SPARK.Pointers.Auto_Reclaimed.Global_Memory (Cell);
   use Ptrs;
   use Ptrs.Memory_Model;

   package Ops is new Ptrs.Handle_Operations (My_Handles);
   use Ops;

   function Id (C : Cell) return Cell is (C);
   package Cell_Ops is new Ptrs.Copy_Operations (Id);
   use Cell_Ops;

   --  Dereferencing a pointer the model does not say is valid. A Pointer
   --  value alone proves nothing about the memory.

   procedure Deref_Unvalidated (P : Pointer)
   with Global => Ptrs.Memory
   is
      C : Cell;
   begin
      C := Deref (P);  --  @PRECONDITION:FAIL
      pragma Assert (C.V = C.V);
   end Deref_Unvalidated;

   --  Assuming a write through one pointer leaves another alone. Nothing
   --  says P and Q designate different cells, which is the whole point of
   --  the explicit memory model.

   procedure Aliasing_Is_Possible (P, Q : Pointer)
   with
     Global => (In_Out => Ptrs.Memory),
     Pre    => (Static => In_Memory (Model, P) and then In_Memory (Model, Q))
   is
      Before : constant Integer := Deref (Q).V;
   begin
      Assign (P, (V => 0));
      pragma Assert (Deref (Q).V = Before);  --  @ASSERT:FAIL
   end Aliasing_Is_Possible;

   --  Converting a handle that is not known to belong to this instantiation.
   --  Valid_Handle is what ties a handle to one, and handles are reinterpreted
   --  bit patterns, so using the wrong one would be a type confusion.

   procedure Strong_Handle_Unvalidated (H : Strong_Handle)
   with Global => null
   is
      P : Pointer;
   begin
      P := Of_Strong_Handle (H);  --  @PRECONDITION:FAIL
      pragma Assert (P = P);
   end Strong_Handle_Unvalidated;

   --  Assuming a weak handle still resolves. It makes no claim on the cell,
   --  so the cell may already be reclaimed and the result null.

   procedure Weak_May_Be_Dead (W : Weak_Handle)
   with
     Global => (Input => SPARK.Pointers.Memory_Addresses),
     Pre    => (SPARKlib_Full => Valid_Handle (W))
   is
      P : constant Pointer := Of_Weak_Handle (W);
   begin
      pragma Assert (P /= Null_Pointer);  --  @ASSERT:FAIL
   end Weak_May_Be_Dead;

   --  Assuming a weak handle resolves to the pointer it was made from,
   --  without supplying a witness that the cell is still alive. This is
   --  exactly what Witnessed_Conversions exists to let a caller establish.

   procedure Weak_Is_Not_Its_Target (W : Weak_Handle)
   with
     Global => (Input => SPARK.Pointers.Memory_Addresses),
     Pre    => (SPARKlib_Full => Valid_Handle (W))
   is
      P : constant Pointer := Of_Weak_Handle (W);
   begin
      pragma Assert (Static => P = Peek (W));  --  @ASSERT:FAIL
   end Weak_Is_Not_Its_Target;

begin
   null;
end Pointers_Soundness;
