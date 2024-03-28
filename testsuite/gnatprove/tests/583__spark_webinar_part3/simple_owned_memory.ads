package Simple_Owned_Memory
  with SPARK_Mode
is
   subtype Str is String(1..5);

   type Chunk is private
     with Annotate =>
       (GNATprove, Ownership, "Needs_Reclamation");

   function Is_Null (C : Chunk) return Boolean
   with
     Annotate => (GNATprove, Ownership, "Is_Reclaimed"),
     Post => Is_Null'Result = (State(C) = Freed);

   type Status is (Allocated, Initialized, Freed) with Ghost;

   function State (C : Chunk) return Status
   with
     Ghost, Import, Global => null;

   function Alloc return Chunk
   with
     Global => null,
     Post => State(Alloc'Result) = Allocated;

   procedure Free (C : in out Chunk)
   with
     Global => null,
     Post => State(C) = Freed;

   procedure Write (C : in out Chunk; Data : Str)
   with
     Global => null,
     Pre  => State(C) in Allocated | Initialized,
     Post => State(C) in Initialized
       and then Read(C) = Data;

   function Read (C : Chunk) return Str
   with
     Global => null,
     Pre => State(C) in Initialized;

private
   pragma SPARK_Mode (Off);

   type Chunk is access Str;

   function Is_Null (C : Chunk) return Boolean is (C = null);

end Simple_Owned_Memory;
