procedure AAlias
with
   SPARK_Mode
is
   type M64_Type is mod 2**64;
   type Byte is mod 2**8;

   type X_Type is array (M64_Type range <>) of Byte;

   procedure Swap_Elements (E1, E2 : in out Byte)
   with
      Post => (E1 = E2'Old and E2 = E1'Old)
   is
      B : Byte;
   begin
      B  := E1;
      E1 := E2;
      E2 := B;
   end Swap_Elements;

   procedure Swap_Arrays (B1, B2 : in out X_Type)
   with
      Pre => (B1'Length = B2'Length)
   is
   begin
      for I in B1'Range loop
         Swap_Elements (B1 (I), B2 (I - B1'First + B2'First));
      end loop;
   end Swap_Arrays;

   A : X_Type (0 .. 1000) := (others => 42);

begin
   Swap_Arrays (A (10..20), A (50..60));
end AAlias;
