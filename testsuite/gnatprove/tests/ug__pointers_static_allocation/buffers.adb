with SPARK.Pointers.Static_Allocation;

procedure Buffers with SPARK_Mode is
   function Create_Object return String is (1 .. 4 => ' ');
   package Storage is new SPARK.Pointers.Static_Allocation
     (String, Create_Object);
   use Storage;

   Buffer : Object_Access := P;
begin
   pragma Assert (Buffer /= null and then Buffer.all = "    ");

   declare
      B : access String := Buffer;
   begin
      B (1) := 'A';
   end;
   pragma Assert (Buffer.all = "A   ");

   P := Buffer;
   pragma Assert (P.all = "A   ");
end Buffers;
