package Simple_Memory
  with SPARK_Mode
is
   subtype Str is String(1..5);

   type Chunk is limited private;

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
     Post => State(C) = Initialized
       and then Read(C) = Data;

   function Read (C : Chunk) return Str
   with
     Global => null,
     Pre => State(C) = Initialized;

private
   pragma SPARK_Mode (Off);

   type Chunk is access Str;

end Simple_Memory;
