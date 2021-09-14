with Interfaces; use Interfaces;

generic
   type Object (<>) is private;
package Hidden_Pointers with
  SPARK_Mode,
  Annotate => (GNATprove, Terminating)
is
   pragma Unevaluated_Use_Of_Old (Allow);

   --  Identity function on objects. As the library copies objects inside
   --  code annotated with SPARK_Mode => Off, we need to make sure that such
   --  copies are allowed by SPARK.
   function Check_No_Deep_Objects (O : Object) return Object is (O) with Ghost;

   --  Model for the memory, this is not executable
   package Model with Ghost is
      type Memory is private with
        Default_Initial_Condition,
        Iterable => (First       => Iter_First,
                     Next        => Iter_Next,
                     Has_Element => Iter_Has_Element,
                     Element     => Iter_Element);

      --  Whether an address designates some valid data in the memory
      function Valid (M : Memory; A : Integer_64) return Boolean with
        Import,
        Post => (if Valid'Result then A /= 0);
      --  Access the data at a given address in the memory
      function Get (M : Memory; A : Integer_64) return Object with Import,
        Pre => Valid (M, A);

      --  Provide for .. of quantification on valid pointers.
      --  These subprograms should not be used directly.
      type Private_Key is private;
      function Iter_First (M : Memory) return Private_Key with Import;
      function Iter_Has_Element (M : Memory; K : Private_Key) return Boolean with Import;
      function Iter_Next (M : Memory; K : Private_Key) return Private_Key with Import;
      function Iter_Element (M : Memory; K : Private_Key) return Integer_64 with Import;
      pragma Annotate (GNATprove, Iterable_For_Proof, "Contains", Valid);

   private
      pragma SPARK_Mode (Off);
      type Memory is null record;
      type Private_Key is new Integer;
   end Model;

   use Model;
   My_Memory : Memory with Ghost;

   type Pointer is private with
     Default_Initial_Condition => Address (Pointer) = 0;
   function Null_Pointer return Pointer with
     Global => null,
     Post => Address (Null_Pointer'Result) = 0;
   function Address (P : Pointer) return Integer_64;

   function "=" (P1, P2 : Pointer) return Boolean with
     Global => null,
     Post => "="'Result = (Address (P1) = Address (P2)),
     Annotate => (GNATprove, Inline_For_Proof);

   procedure Create (O : Object; P : out Pointer) with
     Global => (In_Out => My_Memory),
     Post => Valid (My_Memory, Address (P))
     and then (for all Q of My_Memory => Address (P) = Q or else Valid (My_Memory'Old, Q))
     and then (for all Q of My_Memory'Old => Address (P) /= Q and then Valid (My_Memory, Q))
     and then (for all Q of My_Memory'Old => Get (My_Memory, Q) = Get (My_Memory'Old, Q))
     and then Deref (P) = O;

   function Deref (P : Pointer) return Object with
     Global => My_Memory,
     Pre => Valid (My_Memory, Address (P)),
     Post => Deref'Result = Get (My_Memory, Address (P)),
     Annotate => (GNATprove, Inline_For_Proof);

   procedure Assign (P : Pointer; O : Object) with
     Global => (In_Out => My_Memory),
     Pre => Valid (My_Memory, Address (P)),
     Post => Valid (My_Memory, Address (P))
     and then Get (My_Memory, Address (P)) = O
     and then (for all Q of My_Memory => Valid (My_Memory'Old, Q))
     and then (for all Q of My_Memory'Old => Valid (My_Memory, Q))
     and then (for all Q of My_Memory =>
                 (if Q /= Address (P) then Get (My_Memory, Q) = Get (My_Memory'Old, Q)));

   procedure Dealloc (P : in out Pointer) with
     Global => (In_Out => My_Memory),
     Pre => Valid (My_Memory, Address (P)) or P = Null_Pointer,
     Post => not Valid (My_Memory, Address (P)'Old)
     and then P = Null_Pointer
     and then (for all Q of My_Memory'Old => Address (P)'Old = Q or else Valid (My_Memory, Q))
     and then (for all Q of My_Memory => Address (P)'Old /= Q and then Valid (My_Memory'Old, Q))
     and then (for all Q of My_Memory => Get (My_Memory, Q) = Get (My_Memory'Old, Q));
private
   pragma SPARK_Mode (Off);
   type Pointer_B is access Object;
   function Eq (P1, P2 : Pointer_B) return Boolean renames "=";
   type Pointer is new Pointer_B;
end Hidden_Pointers;
