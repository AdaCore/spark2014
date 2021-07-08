with Bytes; use Bytes;

procedure Use_Bytes_Gen is

   type Rec is record
      A, B, C : Integer;
   end record with Size => 96, Alignment => 4, Object_Size => 96;

   R : aliased Rec := (0, 1, 41);

   function Extract_Gen is new Extract (Rec);
   procedure Extract_Proc_Gen is new Extract_Proc (Rec);

begin
   pragma Assert (Extract_Gen (R) = 42);
end Use_Bytes_Gen;
