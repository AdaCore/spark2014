with Ada.Unchecked_Deallocation;

package body Memory
  with SPARK_Mode
is
   function Alloc (Siz : Positive) return Chunk is
   begin
      return new Str'(1 .. Siz => ' ');
   end Alloc;

   procedure Free (C : in out Chunk) is
      procedure UD is new Ada.Unchecked_Deallocation (Str, Chunk);
   begin
      UD (C);
   end Free;

   procedure Write (C : in out Chunk; From : Positive; Data : String) is
   begin
      C(From .. From - 1 + Data'Length) := Str(Data);
   end Write;

end Memory;
