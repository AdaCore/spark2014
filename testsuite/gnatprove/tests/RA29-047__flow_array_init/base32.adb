package body Base32
  with SPARK_Mode
is

   ------------
   -- Decode --
   ------------

   function Decode (S : Base32_String) return Buffer with SPARK_Mode => Off is
      Chunks  : constant Positive := S'Length / 8;
      Decoded : Buffer (1 .. Chunks * 5) := (others => 0);
   begin
      return Decoded;
   end Decode;

   ------------
   -- Encode --
   ------------

   function Encode (B : Buffer) return Base32_String with SPARK_Mode => Off is
      Chunks  : constant Natural := B'Length / 5;
      Encoded : Base32_String (1 .. Chunks * 8) := (others => 'A');
   begin
      return Encoded;
   end Encode;

   -------------------
   -- Decode_String --
   -------------------

   function Decode_String (S : Base32_String) return String
   is
      B : Buffer := Decode (S);
      Decoded_String : String (1 .. B'Length); -- := (others => Character'Val (0));
   begin
      for I in Decoded_String'Range loop
         Decoded_String (I) := '0';
      end loop;
      return Decoded_String;
   end Decode_String;

   -------------------
   -- Encode_String --
   -------------------

   function Encode_String (S : String) return Base32_String
   is
      B : Buffer (1 .. S'Length); -- := (others => 0);
   begin
      for I in B'Range loop
         B (I) := Character'Pos (S (S'First + Integer (I - 1)));
      end loop;
      return Encode (B);
   end Encode_String;

end Base32;
