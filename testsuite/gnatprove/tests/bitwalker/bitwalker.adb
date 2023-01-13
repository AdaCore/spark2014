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

   function Cases64 (I : Integer) return Boolean
   is
     (I = 0 or I = 1 or I = 2 or I = 3
      or I = 4 or I = 5 or I = 6 or I = 7
      or I = 8 or I = 9 or I = 10 or I = 11
      or I = 12 or I = 13 or I = 14 or I = 15
      or I = 16 or I = 17 or I = 18 or I = 19
      or I = 20 or I = 21 or I = 22 or I = 23
      or I = 24 or I = 25 or I = 26 or I = 27
      or I = 28 or I = 29 or I = 30 or I = 31
      or I = 32 or I = 33 or I = 34 or I = 35
      or I = 36 or I = 37 or I = 38 or I = 39
      or I = 40 or I = 41 or I = 42 or I = 43
      or I = 44 or I = 45 or I = 46 or I = 47
      or I = 48 or I = 49 or I = 50 or I = 51
      or I = 52 or I = 53 or I = 54 or I = 55
      or I = 56 or I = 57 or I = 58 or I = 59
      or I = 60 or I = 61 or I = 62 or I = 63)
     with Ghost, Annotate => (GNATprove, Inline_For_Proof);
   --  Explicit case disjunction for the two coming lemmas.

   function Cond_Unit (X : Unsigned_64; Len : Integer; I : Integer)
                       return Boolean
   is
      (if I in Len .. 63 and then 0 <= I then not Nth (X, I))
       with Ghost, Annotate => (GNATprove, Inline_For_Proof);
   function Less_Than_Max_Cond (X : Unsigned_64; Len : Integer) return Boolean
   is
     (Cond_Unit (X, Len, 0) and Cond_Unit (X, Len, 1)
      and Cond_Unit (X, Len, 2) and Cond_Unit (X, Len, 3)
      and Cond_Unit (X, Len, 4) and Cond_Unit (X, Len, 5)
      and Cond_Unit (X, Len, 6) and Cond_Unit (X, Len, 7)
      and Cond_Unit (X, Len, 8) and Cond_Unit (X, Len, 9)
      and Cond_Unit (X, Len, 10) and Cond_Unit (X, Len, 11)
      and Cond_Unit (X, Len, 12) and Cond_Unit (X, Len, 13)
      and Cond_Unit (X, Len, 14) and Cond_Unit (X, Len, 15)
      and Cond_Unit (X, Len, 16) and Cond_Unit (X, Len, 17)
      and Cond_Unit (X, Len, 18) and Cond_Unit (X, Len, 19)
      and Cond_Unit (X, Len, 20) and Cond_Unit (X, Len, 21)
      and Cond_Unit (X, Len, 22) and Cond_Unit (X, Len, 23)
      and Cond_Unit (X, Len, 24) and Cond_Unit (X, Len, 25)
      and Cond_Unit (X, Len, 26) and Cond_Unit (X, Len, 27)
      and Cond_Unit (X, Len, 28) and Cond_Unit (X, Len, 29)
      and Cond_Unit (X, Len, 30) and Cond_Unit (X, Len, 31)
      and Cond_Unit (X, Len, 32) and Cond_Unit (X, Len, 33)
      and Cond_Unit (X, Len, 34) and Cond_Unit (X, Len, 35)
      and Cond_Unit (X, Len, 36) and Cond_Unit (X, Len, 37)
      and Cond_Unit (X, Len, 38) and Cond_Unit (X, Len, 39)
      and Cond_Unit (X, Len, 40) and Cond_Unit (X, Len, 41)
      and Cond_Unit (X, Len, 42) and Cond_Unit (X, Len, 43)
      and Cond_Unit (X, Len, 44) and Cond_Unit (X, Len, 45)
      and Cond_Unit (X, Len, 46) and Cond_Unit (X, Len, 47)
      and Cond_Unit (X, Len, 48) and Cond_Unit (X, Len, 49)
      and Cond_Unit (X, Len, 50) and Cond_Unit (X, Len, 51)
      and Cond_Unit (X, Len, 52) and Cond_Unit (X, Len, 53)
      and Cond_Unit (X, Len, 54) and Cond_Unit (X, Len, 55)
      and Cond_Unit (X, Len, 56) and Cond_Unit (X, Len, 57)
      and Cond_Unit (X, Len, 58) and Cond_Unit (X, Len, 59)
      and Cond_Unit (X, Len, 60) and Cond_Unit (X, Len, 61)
      and Cond_Unit (X, Len, 62) and Cond_Unit (X, Len, 63))
       with Ghost, Annotate => (GNATprove, Inline_For_Proof);
   --  Break down the quantified expressions in the hypothesis/
   --  cases to prove.

   procedure Lemma_Less_Than_Max (X : Unsigned_64; Len : Integer) is
   begin
      pragma Assert (Cases64 (Len));
      pragma Assert (Less_Than_Max_Cond (X, Len));
   end;

   procedure Lemma_Less_Than_Max2 (X : Unsigned_64; Len : Integer) is
   begin
      pragma Assert (Cases64 (Len));
      pragma Assert (Less_Than_Max_Cond (X, Len));
   end;

   procedure Lemma_Nth_Eq (X, Y : Unsigned_64) is
      procedure Prove_Next_Iter (X : Unsigned_64; I : Integer) with
        Pre  => I in 0 .. 63,
        Post => Shift_Right (X, I) =
          Shift_Left (Shift_Right (X, I + 1), 1)
            + (if Nth (X, I) then 1 else 0);

      procedure Prove_Next_Iter (X : Unsigned_64; I : Integer) is null;
   begin
      for I in reverse 0 .. 63 loop
         Prove_Next_Iter (X, I);
         Prove_Next_Iter (Y, I);
         pragma Loop_Invariant (Shift_Right (X, I) = Shift_Right (Y, I));
      end loop;
   end Lemma_Nth_Eq;

   procedure PeekThenPoke (Start, Len : Natural;
                           Addr       : in out Byte_Sequence;
                           Result     : out Integer)
   is
      Value : Unsigned_64;
      AddrOld  : constant Byte_Sequence := Addr with Ghost;
   begin
      Value := Peek (Start, Len, Addr);

      Lemma_Less_Than_Max (Value, Len);

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
   begin
      Lemma_Less_Than_Max2 (Value, Len);

      Poke (Start, Len, Addr, Value, PokeResult);

      pragma Assert (PokeResult = 0);

      Result := Peek (Start, Len, Addr);

      Lemma_Nth_Eq (Value, Result);
   end PokeThenPeek;

end Bitwalker;
