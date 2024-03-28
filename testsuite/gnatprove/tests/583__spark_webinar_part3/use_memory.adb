with Memory; use Memory;

procedure Use_Memory
  with SPARK_Mode
is
   C : Chunk := Alloc(11);
begin
   pragma Assert (Read (C, 1, 11) = "error");

   Write(C, 1, "hello ");
   pragma Assert (Read(C, 1, 6) = "hello ");

   Write(C, 7, "world");
   pragma Assert (Read(C, 1, 11) = "hello world");

   Free(C);

   Write(C, 1, "error");

end Use_Memory;
