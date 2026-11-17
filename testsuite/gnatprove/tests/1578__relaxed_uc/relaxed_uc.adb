with Ada.Unchecked_Conversion;

package body Relaxed_UC with SPARK_Mode is
   use type Interfaces.Unsigned_8;
   use type Word;

   function To_Word is new Ada.Unchecked_Conversion (Bytes, Word);
   function To_Bytes is new Ada.Unchecked_Conversion (Word, Bytes);

   -------------
   -- Precise --
   -------------

   procedure Precise is
      type Box is record
         Value : Word;
      end record with Relaxed_Initialization, Size => 32, Alignment => 4;
      for Box use record
         Value at 0 range 0 .. 31;
      end record;
      type Nested is record
         Data : Bytes;
      end record with Size => 32, Alignment => 4;
      for Nested use record
         Data at 0 range 0 .. 31;
      end record;
      type Mixed is record
         Ordinary : Word;
         Data : Bytes;
      end record with Size => 64, Alignment => 8;
      for Mixed use record
         Ordinary at 0 range 0 .. 31;
         Data at 4 range 0 .. 31;
      end record;
      function To_Mixed is new Ada.Unchecked_Conversion
        (Interfaces.Unsigned_64, Mixed);
      function To_Box is new Ada.Unchecked_Conversion (Bytes, Box);
      function To_Nested is new Ada.Unchecked_Conversion (Box, Nested);
      function Identity is new Ada.Unchecked_Conversion (Bytes, Bytes);
      X : Bytes := (others => (Value => 16#11#));
      W : Word := To_Word (X);
      Y : Bytes := To_Bytes (W);
      B : Box := To_Box (X);
      N : Nested := To_Nested (B);
      Z : Bytes := Identity (Y);
      M : Mixed := To_Mixed (16#1111_1111_1111_1111#);
   begin
      pragma Assert (W = 16#1111_1111#);
      pragma Assert (Y'Initialized);
      pragma Assert (Y = X);
      pragma Assert (B'Initialized);
      pragma Assert (B.Value = W);
      pragma Assert (N'Initialized);
      pragma Assert (N.Data = X);
      pragma Assert (Z'Initialized);
      pragma Assert (Z = X);
      pragma Assert (M.Data'Initialized);
      pragma Assert (M.Ordinary = W and M.Data = X);
   end Precise;

   ---------------
   -- Imprecise --
   ---------------

   procedure Imprecise is
      --  More than 128 bits prevents precise bitvector handling.

      type Plain is array (1 .. 20) of Interfaces.Unsigned_8
        with Component_Size => 8;
      type Relaxed is array (1 .. 19) of Byte
        with Component_Size => 8;
      type Nested is record
         Ordinary : Interfaces.Unsigned_8;
         Data : Relaxed;
      end record with Size => 160, Alignment => 1;
      for Nested use record
         Ordinary at 0 range 0 .. 7;
         Data at 1 range 0 .. 151;
      end record;
      type All_Relaxed is array (1 .. 20) of Byte
        with Component_Size => 8;
      function Convert is new Ada.Unchecked_Conversion (Plain, Nested);
      function Reverse_Convert is new Ada.Unchecked_Conversion (Nested, Plain);
      function To_Relaxed is new Ada.Unchecked_Conversion (Nested, All_Relaxed);
      X : Plain := (others => 0);
      Y : Nested := Convert (X);
      Z : Plain := Reverse_Convert (Y);
      R : All_Relaxed := To_Relaxed (Y);
   begin
      pragma Assert (Y.Data'Initialized);
      pragma Assert (Y.Data (1).Value'Initialized);
      pragma Assert (R'Initialized);
      pragma Assert (Z = X);
   end Imprecise;

   --------------------
   -- Partial_Source --
   --------------------

   procedure Partial_Source (X : Bytes; Result : out Word) is
   begin
      Result := To_Word (X); -- @INIT_BY_PROOF:FAIL
   end Partial_Source;

   ---------------------------
   -- Object_Relaxed_Source --
   ---------------------------

   procedure Object_Relaxed_Source (Result : out Word) is
      type Plain is array (1 .. 4) of Interfaces.Unsigned_8
        with Component_Size => 8, Alignment => 4;
      function Convert is new Ada.Unchecked_Conversion (Plain, Word);
      X : Plain with Relaxed_Initialization;
   begin
      X (1) := 0;
      Result := Convert (X); -- @INIT_BY_PROOF:FAIL
   end Object_Relaxed_Source;
end Relaxed_UC;
