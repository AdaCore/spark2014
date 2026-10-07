--  Soundness test for SPARK.Pointers.Poisoned.Pointers. Every check marked
--  FAIL is a dangerous operation SPARK has to reject. The checks marked PASS
--  are the model facts those rejections rest on; they are here so that
--  weakening one of them breaks this test rather than going unnoticed.

with SPARK.Pointers.Poisoned.Pointers;

procedure Poisoned_Soundness with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);
   --  Required to instantiate Array_Operations: its contracts use Copy (A)'Old
   --  under quantifiers.

   type Index is range 1 .. 10;

   type Object is record
      V : Natural;
   end record;

   package Pointers is new
     SPARK.Pointers.Poisoned.Pointers (Object);
   use Pointers;

   function Id (O : Object) return Object is (O);
   function Create_Pointer is new Pointers.Create (Object, Id);

   --  Reading a holder whose contents have been taken out of it. Take leaves
   --  the source poisoned, and a poisoned holder is not a Readable_Pointer, which
   --  is the subtype every accessor takes.

   procedure Read_After_Take is
      H : Pointer := Create_Pointer ((V => 1));
      G : Pointer;
      N : Natural;
   begin
      G := Take (H);
      N := Constant_Reference (H).V;  --  @PREDICATE_CHECK:FAIL
      pragma Assert (N = N);
      Reclaim (G);
   end Read_After_Take;

   --  Reading a holder that designates nothing. A default-initialised holder
   --  is Null_Pointer, which is not poisoned, so the predicate lets it through
   --  and the precondition of the accessor is what rejects it.

   procedure Read_Null is
      H : Pointer;
      N : Natural;
   begin
      N := Constant_Reference (H).V;  --  @PRECONDITION:FAIL
      pragma Assert (N = N);
   end Read_Null;

   type Pointer_Array is array (Index range <>) of Pointer;
   package Arrays is new Pointers.Array_Operations (Index, Pointer_Array);
   use Arrays;

   --  Relocate poisons the cells it moves out of, it does not null them. The
   --  slice below shifts 5 .. 7 down onto 1 .. 3, so 5 .. 7 are source cells
   --  outside the target range. A (9) is null and plays no part; it is there
   --  because a wrong index in the postcondition of Relocate used to read it
   --  in place of A (5) and hand the caller the opposite conclusion.

   procedure Moved_Out_Is_Not_Null (A : in out Pointer_Array)
   with
     Global => null,
     Pre    =>
       (Static =>
          A'First = 1
          and then A'Last = 10
          and then (for all I in Index range 1 .. 3 => Is_Reclaimed (A (I)))
          and then A (9) = Null_Pointer
          and then (for all I in Index range 5 .. 7 =>
                      not Is_Poisoned (A (I)) and then A (I) /= Null_Pointer))
   is
   begin
      Relocate (A, 5, 7, 1, 3);
      pragma Assert (Static => Is_Poisoned (A (5)));  --  @ASSERT:PASS
      pragma Assert (Static => A (5) = Null_Pointer);  --  @ASSERT:FAIL
   end Moved_Out_Is_Not_Null;

begin
   --  Null_Pointer is not poisoned. Poisoning means "moved out of", and
   --  Null_Pointer was never moved out of, so the two states are independent.
   --  This is what keeps the Null_Pointer branches in the contracts of Take,
   --  Move and Reclaim reachable, and what makes Is_Poisoned entail that a
   --  holder is not null.

   pragma Assert (Static => not Is_Poisoned (Null_Pointer));  --  @ASSERT:PASS
end Poisoned_Soundness;
