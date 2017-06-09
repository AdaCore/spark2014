package body Bitwalker with
  SPARK_Mode
is
   --------------
   -- PeekBit8 --
   --------------

   function PeekBit8 (Byte : Unsigned_8; Left : Natural) return Boolean
   is
      Ret : constant Boolean := (Byte and Shift_Left (1, 7 - Left)) /= 0;
   begin
      return Ret;
   end PeekBit8;

   ---------------
   -- PokeBit64 --
   ---------------

   function PokeBit64
      (Value : Unsigned_64;
       Left  : Natural;
       Flag  : Boolean) return Unsigned_64
   is
      Left_Bv : constant Unsigned_64 := Unsigned_64(Left);
   begin
      pragma Assert (Left_Bv < 64);
      pragma Assert (63 - Left_Bv = Unsigned_64 (63 - Left));

      declare
         Mask : constant Unsigned_64 := Shift_Left (1, 63 - Left);
         R : constant Unsigned_64 :=
           (if Flag then (Value or Mask) else (Value and (not Mask)));
      begin
         pragma Assert (for all I in Unsigned_64
                        range 0 .. 63 =>
                          (if I /= 63 - Left_Bv then
                              Nth_Bv (R, I) = Nth_Bv (Value, I)));

         pragma Assert (for all I in Natural
                        range 0 .. 63 =>
                          (0 <= Unsigned_64 (I) and then
                           Unsigned_64 (I) <= 63));

         pragma Assert (Flag = Nth_Bv (R, 63 - Left_Bv));

         return R;
      end;
   end PokeBit64;

   ----------
   -- Peek --
   ----------

   function Peek
     (Start, Length : Natural;
      Addr          : Byte_Sequence) return Unsigned_64 is
   begin
      if Start + Length > 8 * Addr'Length then
         return 0;
      end if;

      declare
         Retval : Unsigned_64 := 0;
         Flag   : Boolean;
      begin
         for I in 0 .. Length - 1 loop
            pragma Loop_Invariant
              (for all J in Length - I .. Length - 1 =>
                 Nth8_Stream (Addr, Start + Length - J - 1)
               = Nth (Retval, J));

            pragma Loop_Invariant
              (for all J in Length .. 63 =>
                 not Nth (Retval, J));

            Flag := PeekBit8Array (Addr, Start + I);
            Retval := PokeBit64 (Retval, (64 - Length) + I, Flag);
         end loop;

         return Retval;
      end;
   end Peek;

   function PokeBit8 (Byte : Unsigned_8;
                      Left : Natural;
                      Flag : Boolean)
                      return Unsigned_8
   is
      Mask : constant Unsigned_8 := Shift_Left (1, 7 - Left);
      R : constant Unsigned_8 := (if Flag then
                                    (Byte or Mask)
                                  else
                                    (Byte and (not Mask)));
      Left_Bv : constant Unsigned_8 := Unsigned_8 (Left) with Ghost;
   begin
      pragma Assert (Left_Bv < 8);
      pragma Assert (7 - Left_Bv = Unsigned_8 (7 - Left));

      pragma Assert ((for all I in Unsigned_8 range 0 .. 7 =>
                        (if I /= 7 - Left_Bv then
                            Nth_Bv (R, I) = Nth_Bv (Byte, I))));
      pragma Assert (Nth_Bv (R, 7 - Left_Bv) = Flag);
      return R;
   end PokeBit8;

   procedure PokeBit8Array (Addr : in out Byte_Sequence;
                            Left : Natural;
                            Flag : Boolean)
   is
   begin
      Addr (Left / 8) := PokeBit8 (Addr(Left / 8), Left rem 8, Flag);
   end PokeBit8Array;

   procedure Poke (Start, Len : Natural;
                   Addr       : in out Byte_Sequence;
                   Value      : Unsigned_64;
                   Result     : out Integer)
   is
      Flag : Boolean;
   begin
      if Start + Len > Addr'Length * 8 then
         Result := -1;
         return;
      elsif Value >= MaxValue (Len) then
         Result := -2;
         return;
      end if;

      for I in 0 .. Len - 1 loop
         pragma Loop_Invariant (I in 0 .. Len);
         pragma Loop_Invariant
           (for all J in 0 .. Start - 1 =>
              Nth8_Stream (Addr'Loop_Entry, J) = Nth8_Stream (Addr, J));
         pragma Loop_Invariant
           (for all J in Start .. Start + I - 1 =>
              Nth8_Stream (Addr, J) = Nth (Value, Len - J - 1 + Start));
         pragma Loop_Invariant
           (for all J in Start + I .. 8 * Addr'Length - 1 =>
              Nth8_Stream (Addr, J) = Nth8_Stream (Addr'Loop_Entry, J));

         Flag := PeekBit64 (Value, (64 - Len) + I);

         PokeBit8Array (Addr,
                        Start + I,
                        Flag);

         pragma Assert (Nth8_Stream (Addr, Start + I)
                      = Nth (Value, Len - I - 1));
         pragma Assert
           (for all K in Start .. Start + I - 1 =>
              K /= Start + I and then
            K in 0 .. 8 * Addr'Length - 1 and then
            Nth8_Stream (Addr, K) = Nth (Value, Start + Len - K - 1));
      end loop;

      Result := 0;
   end Poke;

  function LemmaFunction (X : Unsigned_64; Len : Integer) return Unit is
      Len_Bv : constant Unsigned_64 := Unsigned_64 (Len);
   begin
      pragma Assert (for all J in Len .. Len + (64 - Len) - 1 =>
                       Nth (X, J) = Nth (Unsigned_64 (0), J));
      pragma Assert (Eq_Sub (X, 0, Natural (Len_Bv), Natural (64 - Len_Bv)));
      pragma Assert (Eq_Sub_Bv (X, 0, Len_Bv, 64 - Len_Bv));
      pragma Assert_And_Cut ((X and (MaxValue (Len) - 1)) = X);
      pragma Assert (Unsigned_64 (Len) in 0 .. 63);
      return Void;
   end LemmaFunction;

   function LemmaFunction2 (X : Unsigned_64; Len : Integer) return Unit is
      Len_Bv : constant Unsigned_64 := Unsigned_64 (Len);
   begin
      pragma Assert ((X and (MaxValue (Len) - 1)) = X);
      pragma Assert (Eq_Sub_Bv (X, 0, Len_Bv, 64 - Len_Bv));
      pragma Assert (Eq_Sub (X, 0, Natural (Len_Bv), Natural (64 - Len_Bv)));
      pragma Assert (for all J in Len .. Len + (64 - Len) - 1 =>
                       Nth (X, J) = Nth (Unsigned_64 (0), J));
      return Void;
   end LemmaFunction2;

   procedure PeekThenPoke (Start, Len : Natural;
                           Addr       : in out Byte_Sequence;
                           Result     : out Integer)
   is
      Value : Unsigned_64;
      AddrOld  : constant Byte_Sequence := Addr with Ghost;
      V : Unit with Ghost;
   begin
      Value := Peek (Start, Len, Addr);

      V := LemmaFunction (Value, Len);

      Poke (Start, Len, Addr, Value, Result);

      pragma Assert (Result = 0);

      pragma Assert
        (for all I in Start .. Start + Len - 1 =>
           Nth8_Stream (Addr, I) = Nth8_Stream (AddrOld, I));
   end PeekThenPoke;


   procedure PokeThenPeek (Start, Len : Natural;
                           Addr : in out Byte_Sequence;
                           Value : Unsigned_64;
                           Result : out Unsigned_64)
   is
      PokeResult : Integer;
      V : Unit with Ghost;
   begin
      V := LemmaFunction2 (Value, Len);

      Poke (Start, Len, Addr, Value, PokeResult);

      pragma Assert (PokeResult = 0);

      Result := Peek (Start, Len ,Addr);

      pragma Assert (Eq (Result, Value));
   end PokeThenPeek;

end Bitwalker;
