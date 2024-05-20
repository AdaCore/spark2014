with Ada.Unchecked_Deallocation;

package body Simple_Memory
  with SPARK_Mode => Off
is
   function Alloc return Chunk is
   begin
      return new Str;
   end Alloc;

   procedure Free (C : in out Chunk) is
      procedure UD is new Ada.Unchecked_Deallocation (Str, Chunk);
   begin
      UD (C);
   end Free;

   procedure Write (C : in out Chunk; Data : Str) is
   begin
      C.all := Data;
   end Write;

   function Read (C : Chunk) return Str is
     (C.all);

end Simple_Memory;
