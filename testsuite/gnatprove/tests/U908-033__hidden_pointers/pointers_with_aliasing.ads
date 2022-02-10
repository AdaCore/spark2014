with Interfaces; use Interfaces;

generic
   type Object (<>) is private;
package Pointers_With_Aliasing with
  SPARK_Mode,
  Annotate => (GNATprove, Terminating)
is
   pragma Unevaluated_Use_Of_Old (Allow);

   --  Identity function on objects. As the library copies objects inside
   --  code annotated with SPARK_Mode => Off, we need to make sure that such
   --  copies are allowed by SPARK.
   function Check_No_Deep_Objects (O : Object) return Object is (O) with Ghost;

   --  Model for the memory, this is not executable
   package Memory_Model is
      type Address_Type is new Long_Long_Integer;

      type Memory_Type is private with
        Default_Initial_Condition,
        Iterable => (First       => Iter_First,
                     Next        => Iter_Next,
                     Has_Element => Iter_Has_Element,
                     Element     => Iter_Element);

      --  Whether an address designates some valid data in the memory
      function Valid (M : Memory_Type; A : Address_Type) return Boolean with
        Ghost,
        Import,
        Post => (if Valid'Result then A /= 0);
      --  Access the data at a given address in the memory
      function Get (M : Memory_Type; A : Address_Type) return Object with
        Ghost,
        Import,
        Pre => Valid (M, A);

      --  Provide for .. of quantification on valid pointers.
      --  These subprograms should not be used directly.
      type Private_Key is private with Ghost;
      function Iter_First (M : Memory_Type) return Private_Key with Ghost, Import;
      function Iter_Has_Element (M : Memory_Type; K : Private_Key) return Boolean with Ghost, Import;
      function Iter_Next (M : Memory_Type; K : Private_Key) return Private_Key with Ghost, Import;
      function Iter_Element (M : Memory_Type; K : Private_Key) return Address_Type with Ghost, Import;
      pragma Annotate (GNATprove, Iterable_For_Proof, "Contains", Valid);

   private
      pragma SPARK_Mode (Off);
      type Memory_Type is null record;
      type Private_Key is new Integer;
   end Memory_Model;

   use Memory_Model;
   Memory : aliased Memory_Type;

   type Pointer is private with
     Default_Initial_Condition => Address (Pointer) = 0;
   function Null_Pointer return Pointer with
     Global => null,
     Post => Address (Null_Pointer'Result) = 0;
   function Address (P : Pointer) return Address_Type with
     Global => null;

   function "=" (P1, P2 : Pointer) return Boolean with
     Global => null,
     Post => "="'Result = (Address (P1) = Address (P2)),
     Annotate => (GNATprove, Inline_For_Proof);

   procedure Create (O : Object; P : out Pointer) with
     Global => (In_Out => Memory),
     Post => Valid (Memory, Address (P))
     and then (for all Q of Memory => Address (P) = Q or else Valid (Memory'Old, Q))
     and then (for all Q of Memory'Old => Address (P) /= Q and then Valid (Memory, Q))
     and then (for all Q of Memory'Old => Get (Memory, Q) = Get (Memory'Old, Q))
     and then Deref (P) = O;

   --  Primitives for classical pointer functionalities. Deref will copy the
   --  designated value.

   function Deref (P : Pointer) return Object with
     Global => Memory,
     Pre => Valid (Memory, Address (P)),
     Post => Deref'Result = Get (Memory, Address (P)),
     Annotate => (GNATprove, Inline_For_Proof);

   procedure Assign (P : Pointer; O : Object) with
     Global => (In_Out => Memory),
     Pre => Valid (Memory, Address (P)),
     Post => Valid (Memory, Address (P))
     and then Get (Memory, Address (P)) = O
     and then (for all Q of Memory => Valid (Memory'Old, Q))
     and then (for all Q of Memory'Old => Valid (Memory, Q))
     and then (for all Q of Memory =>
                 (if Q /= Address (P) then Get (Memory, Q) = Get (Memory'Old, Q)));

   procedure Dealloc (P : in out Pointer) with
     Global => (In_Out => Memory),
     Pre => Valid (Memory, Address (P)) or P = Null_Pointer,
     Post => not Valid (Memory, Address (P)'Old)
     and then P = Null_Pointer
     and then (for all Q of Memory'Old => Address (P)'Old = Q or else Valid (Memory, Q))
     and then (for all Q of Memory => Address (P)'Old /= Q and then Valid (Memory'Old, Q))
     and then (for all Q of Memory => Get (Memory, Q) = Get (Memory'Old, Q));

   --  Primitives to access the content of a memory cell directly. Ownership is
   --  used to preserve the link between the dereferenced value and the
   --  memory model.

   function Constant_Access (Memory : Memory_Type; P : Pointer) return not null access constant Object with
     Global => null,
     Pre => Valid (Memory, Address (P)),
     Post => Constant_Access'Result.all = Get (Memory, Address (P));

   function At_End (X : access constant Object) return access constant Object is
     (X)
   with Ghost,
       Annotate => (GNATprove, At_End_Borrow);

   function At_End (X : access constant Memory_Type) return access constant Memory_Type is
     (X)
   with Ghost,
       Annotate => (GNATprove, At_End_Borrow);

   function Reference (Memory : not null access Memory_Type; P : Pointer) return not null access Object with
     Global => null,
     Pre => Valid (Memory.all, Address (P)),
     Post => Reference'Result.all = Get (Memory.all, Address (P))
       and then At_End (Reference'Result).all = Get (At_End (Memory).all, Address (P))
       and then (for all Q of At_End (Memory).all => Valid (Memory.all, Q))
       and then (for all Q of Memory.all => Valid (At_End (Memory).all, Q))
       and then (for all Q of At_End (Memory).all =>
                   (if Q /= Address (P) then Get (At_End (Memory).all, Q) = Get (Memory.all, Q)));
private
   pragma SPARK_Mode (Off);
   type Pointer_B is access Object;
   function Eq (P1, P2 : Pointer_B) return Boolean renames "=";
   type Pointer is new Pointer_B;
end Pointers_With_Aliasing;
