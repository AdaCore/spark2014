with Simple_Owned_Memory; use Simple_Owned_Memory;

procedure Use_Simple_Owned_Memory
  with SPARK_Mode
is
   C : Chunk := Alloc;
begin
   Write(C, "hello");
   pragma Assert (Read(C) = "hello");

   Write(C, "world");
   pragma Assert (Read(C) = "world");

   -- Free(C);
   -- pragma Assert (Is_Null(C));

end Use_Simple_Owned_Memory;
