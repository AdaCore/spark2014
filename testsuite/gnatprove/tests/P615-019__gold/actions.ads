package Actions is

   type Status is (Raw, Sanitized, Normalized);
   type Chunk is record
      Data : String (1 .. 256);
      Stat : Status;
   end record;

   procedure Sanitize (C : in out Chunk)
     with Pre  => C.Stat = Raw,
          Post => C.Stat = Sanitized;

   procedure Normalize (C : in out Chunk)
     with Pre  => C.Stat = Sanitized,
          Post => C.Stat = Normalized;

   procedure Main_Treatment (C : in Chunk)
     with Pre => C.Stat = Normalized;

end Actions;
