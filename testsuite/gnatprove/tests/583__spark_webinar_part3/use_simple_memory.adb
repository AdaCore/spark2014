with Simple_Memory; use Simple_Memory;

procedure Use_Simple_Memory
  with SPARK_Mode
is
   C : Chunk := Alloc;
begin
   pragma Assert (State (C) = Allocated);
   pragma Assert (Read (C) = "error");

   Write(C, "hello");
   pragma Assert (State (C) = Initialized);
   pragma Assert (Read(C) = "hello");

   Write(C, "world");
   pragma Assert (Read(C) = "world");

   Free(C);
   pragma Assert (State (C) = Freed);

   Write(C, "error");

end Use_Simple_Memory;
