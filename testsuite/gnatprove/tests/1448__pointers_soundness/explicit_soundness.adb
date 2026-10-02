--  Soundness test for SPARK.Pointers.Explicit_Reclamation.Global_Memory.
--  Every check marked FAIL is a dangerous operation SPARK has to reject.

with SPARK.Pointers.Explicit_Reclamation.Global_Memory;

procedure Explicit_Soundness with SPARK_Mode is

   type Cell is record
      V : Integer;
   end record;

   --  A cell counts as reclaimed once its payload has been zeroed. It stands
   --  in for a cell that owns something the caller has to release first.

   function Is_Reclaimed (C : Cell) return Boolean is (C.V = 0)
   with Ghost => Static;

   package Ptrs is new
     SPARK.Pointers.Explicit_Reclamation.Global_Memory (Cell, Is_Reclaimed);
   use Ptrs;
   use Ptrs.Memory_Model;

   package Ops is new Ptrs.Copy_Operations;
   use Ops;

   --  Reading a pointer after the cell it designated has been deallocated.

   procedure Use_After_Dealloc
   with
     Global =>
       (In_Out => Ptrs.Memory,
        Input  => SPARK.Pointers.Memory_Addresses)
   is
      P : Pointer;
      C : Cell;
   begin
      Ops.Create_Copy ((V => 0), P);
      Dealloc (P);
      C := Deref (P);  --  @PRECONDITION:FAIL
      pragma Assert (C.V = C.V);
   end Use_After_Dealloc;

   --  Deallocating a cell whose contents have not been reclaimed. This is the
   --  obligation that keeps explicit reclamation from leaking what a cell
   --  owns, and it is a precondition rather than something the library can do
   --  for the caller.

   procedure Dealloc_Without_Reclaiming
   with
     Global =>
       (In_Out => Ptrs.Memory,
        Input  => SPARK.Pointers.Memory_Addresses)
   is
      P : Pointer;
   begin
      Ops.Create_Copy ((V => 1), P);
      Dealloc (P);  --  @PRECONDITION:FAIL
   end Dealloc_Without_Reclaiming;

begin
   null;
end Explicit_Soundness;
