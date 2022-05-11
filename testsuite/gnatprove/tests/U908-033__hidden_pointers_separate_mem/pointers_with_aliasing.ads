with Interfaces; use Interfaces;
with Abstract_Maps;
with Unchecked_Deallocation;

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
      type Address_Type is new Unsigned_64;
      --  Address type on 64 bits machines

      package Address_To_Object_Maps is new Abstract_Maps
        (Address_Type, 0, Object);
      --  Use an abstract map rather than a functional map to avoid taking up
      --  memory space as the memory model cannot be ghost.

      type Memory_Map is new Address_To_Object_Maps.Map;

      --  Whether an address designates some valid data in the memory
      function Valid (M : Memory_Map; A : Address_Type) return Boolean renames
        Has_Key;

      --  The memory type should be handled as an ownership type. Currently,
      --  we need to introduce an access type to achieve that. We make it
      --  private so it is not possible to initialize a new Memory_Type from
      --  the content of an existing type.

      type Memory_Type is private;

      function Is_Null_Memory (M : Memory_Type) return Boolean;

      function New_Memory return Memory_Type with
        Post => not Is_Null_Memory (New_Memory'Result);

      function Deref (M : Memory_Type) return Memory_Map with
        Pre => not Is_Null_Memory (M);

      procedure Free_Memory (M : in out Memory_Type) with
        Pre  => Is_Null_Memory (M)
        or else (for all K in Deref (M) => False),
        Post => Is_Null_Memory (M);
      --  To avoid memory leaks, it is not correct to deallocate a memory
      --  containing allocated cells.

      --  Functions to make it easier to specify the frame of subprograms
      --  modifying a memory.

      type Addresses is array (Address_Type) of Boolean with Ghost;

      function None return Addresses is
        ([others => False])
      with Ghost;
      function Only (A : Address_Type) return Addresses is
        ([for Q in Address_Type => (Q = A)])
      with Ghost;

      function Writes
        (M1, M2 : Memory_Map; Target : Addresses) return Boolean
      is
        (for all A in Address_Type =>
           (if not Target (A) and Valid (M1, A) and Valid (M2, A)
            then Get (M1, A) = Get (M2, A)))
       with Ghost;

      function Allocates
        (M1, M2 : Memory_Map; Target : Addresses) return Boolean
      is
        ((for all A in Address_Type =>
            (if Valid (M2, A) then Target (A) or Valid (M1, A)))
         and (for all A in Address_Type =>
                  (if Target (A) then not Valid (M1, A) and Valid (M2, A))))
       with Ghost;

      function Deallocates
        (M1, M2 : Memory_Map; Target : Addresses) return Boolean
      is
        ((for all A in Address_Type =>
            (if Valid (M1, A) then Target (A) or Valid (M2, A)))
         and (for all A in Address_Type =>
                  (if Target (A) then not Valid (M2, A) and Valid (M1, A))))
            with Ghost;

   private
      type Memory_Type is access Memory_Map;

      function New_Memory return Memory_Type is (new Memory_Map'(Empty_Map));

      function Deref (M : Memory_Type) return Memory_Map is (M.all);

      procedure Dealloc_Memory is new
        Unchecked_Deallocation (Memory_Map, Memory_Type);

      procedure Free_Memory (M : in out Memory_Type) renames Dealloc_Memory;

      function Is_Null_Memory (M : Memory_Type) return Boolean is (M = null);
   end Memory_Model;

   use Memory_Model;

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

   procedure Create (Memory : in out Memory_Type; O : Object; P : out Pointer) with
     Global => null,
     Pre  => not Is_Null_Memory (Memory),
     Post => not Is_Null_Memory (Memory)
     and then Valid (Deref (Memory), Address (P))
     and then Allocates (Deref (Memory)'Old, Deref (Memory), Only (Address (P)))
     and then Deallocates (Deref (Memory)'Old, Deref (Memory), None)
     and then Writes (Deref (Memory)'Old, Deref (Memory), None)
     and then Deref (Memory, P) = O;

   --  Primitives for classical pointer functionalities. Deref will copy the
   --  designated value.

   function Deref (Memory : Memory_Type; P : Pointer) return Object with
     Global => null,
     Pre  => not Is_Null_Memory (Memory)
     and then Valid (Deref (Memory), Address (P)),
     Post => Deref'Result = Get (Deref (Memory), Address (P)),
     Annotate => (GNATprove, Inline_For_Proof);

   procedure Assign (Memory : in out Memory_Type; P : Pointer; O : Object) with
     Global => null,
     Pre  => not Is_Null_Memory (Memory)
     and then Valid (Deref (Memory), Address (P)),
     Post => not Is_Null_Memory (Memory)
     and then Get (Deref (Memory), Address (P)) = O
     and then Allocates (Deref (Memory)'Old, Deref (Memory), None)
     and then Deallocates (Deref (Memory)'Old, Deref (Memory), None)
     and then Writes (Deref (Memory)'Old, Deref (Memory), Only (Address (P)));

   procedure Dealloc (Memory : in out Memory_Type; P : in out Pointer) with
     Global => null,
     Pre  => not Is_Null_Memory (Memory)
     and then (Valid (Deref (Memory), Address (P)) or P = Null_Pointer),
     Post => not Is_Null_Memory (Memory)
     and then P = Null_Pointer
     and then Allocates (Deref (Memory)'Old, Deref (Memory), None)
     and then
       (if P'Old = Null_Pointer
        then Deallocates (Deref (Memory)'Old, Deref (Memory), None)
        else Deallocates (Deref (Memory)'Old, Deref (Memory), Only (Address (P)'Old)))
     and then Writes (Deref (Memory)'Old, Deref (Memory), None);

   procedure Move_Memory (Source, Target : in out Memory_Type; P : Pointer) with
   --  Move a pointer from a memory to another.
   --  This is correct because of the implicit invariant that 2 different
   --  memory objects are necessarily disjoint.
     Inline,
     Global => null,
     Pre => not Is_Null_Memory (Source)
     and then not Is_Null_Memory (Target)
     and then Valid (Deref (Source), Address (P)),
     Post => not Is_Null_Memory (Source)
     and then not Is_Null_Memory (Target)
     and then Allocates (Deref (Source)'Old, Deref (Source), None)
     and then Deallocates (Deref (Source)'Old, Deref (Source), Only (Address (P)))
     and then Writes (Deref (Source)'Old, Deref (Source), None)
     and then Allocates (Deref (Target)'Old, Deref (Target), Only (Address (P)))
     and then Deallocates (Deref (Target)'Old, Deref (Target), None)
     and then Writes (Deref (Target)'Old, Deref (Target), None)
     and then Deref (Target, P) = Deref (Source, P)'Old;

   --  Primitives to access the content of a memory cell directly. Ownership is
   --  used to preserve the link between the dereferenced value and the
   --  memory model.

   function Constant_Reference (Memory : Memory_Type; P : Pointer) return not null access constant Object with
     Global => null,
     Pre  => not Is_Null_Memory (Memory)
     and then Valid (Deref (Memory), Address (P)),
     Post => Constant_Reference'Result.all = Get (Deref (Memory), Address (P));

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
     Pre  => not Is_Null_Memory (Memory.all)
     and then Valid (Deref (Memory.all), Address (P)),
     Post => not Is_Null_Memory (At_End (Memory).all)
     and then At_End (Reference'Result).all = Get (Deref (At_End (Memory).all), Address (P))
     and then Allocates (Deref (Memory.all), Deref (At_End (Memory).all), None)
     and then Deallocates (Deref (Memory.all), Deref (At_End (Memory).all), None)
     and then Writes (Deref (Memory.all), Deref (At_End (Memory).all), Only (Address (P)));

private
   pragma SPARK_Mode (Off);
   type Pointer_B is access Object;
   function Eq (P1, P2 : Pointer_B) return Boolean renames "=";
   type Pointer is new Pointer_B;
end Pointers_With_Aliasing;
