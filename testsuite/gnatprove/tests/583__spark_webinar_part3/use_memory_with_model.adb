with Memory_With_Model; use Memory_With_Model;

procedure Use_Memory_With_Model
  with SPARK_Mode
is
   C : Chunk := Alloc(11);
begin
   Write(C, 7, "world");
   pragma Assert (Read(C, 7, 11) = "world");

   Write(C, 1, "hello ");
   pragma Assert (Read(C, 1, 11) = "hello world");

   Free(C);
end Use_Memory_With_Model;
