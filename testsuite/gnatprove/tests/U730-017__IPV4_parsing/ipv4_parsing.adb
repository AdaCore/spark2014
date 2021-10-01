package body IPV4_Parsing with SPARK_Mode is

   -------------------------------------------------------
   -- Body of the Specification-Only Queries and Lemmas --
   -------------------------------------------------------

   function Find_First_Dot (S : String; First : Integer) return Integer is
   begin
      for I in First .. s'Last loop
         if S (I) = '.' then
            return I;
         end if;
         pragma Loop_Invariant (for all K in First .. I => S (K) /= '.');
      end loop;
      return s'Last + 1;
   end Find_First_Dot;

   procedure Lemma_Is_Byte_10_Unique (S : String; First, Last : Integer; V1, V2 : Unsigned_8) with
     Ghost,
     Pre => First in s'Range and then Last in s'Range
     and then Is_Byte_10 (s, First, Last, V1) and then Is_Byte_10 (s, First, Last, V2),
     Post => V1 = V2;
   procedure Lemma_Is_Byte_10_Unique (S : String; First, Last : Integer; V1, V2 : Unsigned_8) is null;

   procedure Lemma_Is_IPV4_Unique (S : String; V1, V2 : Unsigned_32) is
     D1 : constant Positive := Find_First_Dot (S, S'First);
     D2 : constant Positive := Find_First_Dot (S, D1 + 1);
     D3 : constant Positive := Find_First_Dot (S, D2 + 1);
     V1_1 : constant Unsigned_8 := Unsigned_8 (Shift_Right (V1, 24));
     V1_2 : constant Unsigned_8 := Unsigned_8 (Shift_Right (V1, 16) and 16#FF#);
     V1_3 : constant Unsigned_8 := Unsigned_8 (Shift_Right (V1, 8) and 16#FF#);
     V1_4 : constant Unsigned_8 := Unsigned_8 (V1 and 16#FF#);
     V2_1 : constant Unsigned_8 := Unsigned_8 (Shift_Right (V2, 24));
     V2_2 : constant Unsigned_8 := Unsigned_8 (Shift_Right (V2, 16) and 16#FF#);
     V2_3 : constant Unsigned_8 := Unsigned_8 (Shift_Right (V2, 8) and 16#FF#);
     V2_4 : constant Unsigned_8 := Unsigned_8 (V2 and 16#FF#);
   begin
     Lemma_Is_Byte_10_Unique (S, S'First, D1 - 1, V1_1, V2_1);
     Lemma_Is_Byte_10_Unique (S, D1 + 1, D2 - 1, V1_2, V2_2);
     Lemma_Is_Byte_10_Unique (S, D2 + 1, D3 - 1, V1_3, V2_3);
     Lemma_Is_Byte_10_Unique (S, D3 + 1, S'Last, V1_4, V2_4);
   end Lemma_Is_IPV4_Unique;

   -------------------------------
   -- Parsing of IPV4 Addresses --
   -------------------------------

   --  The string is parsed in one pass

   function Byte_Of_Char_10 (c : Digit_10) return Small_Byte_10 is
     (case c is
         when '0' => 0,
         when '1' => 1,
         when '2' => 2,
         when '3' => 3,
         when '4' => 4,
         when '5' => 5,
         when '6' => 6,
         when '7' => 7,
         when '8' => 8,
         when '9' => 9);

   --  Parse the slice of S between First and the first dot if any (the end of
   --  S otherwise) as an Unsigned_8 in base 10. Error is set to False iff this
   --  slice is a valid Unsigned_8. In this case, V is set to this number and
   --  First is modified to designate the first dot in S.
   procedure Parse_Byte_10 (S : String; First : in out Positive; V : out Unsigned_8; Error : out Boolean) with
     Pre  => s'Last < Integer'Last and then First in s'First .. s'Last + 1,
     Post => First in First'Old .. s'Last + 1 and then First - First'Old <= 3
     and then Error = not Valid_Byte_10 (S, First'Old, Find_First_Dot (S, First'Old) - 1)
     and then (if not Error then First = Find_First_Dot (S, First'Old)
                 and then Is_Byte_10 (S, First'Old, First - 1, V))
   is
   begin
      V := 0;
      if First > S'Last or else S (First) not in Digit_10 then
         Error := True;
         return;
      end if;

      for I in 1 .. 3 loop
         V := V * 10 + Byte_Of_Char_10 (S (First));
         First := First + 1;

         if First > S'Last or else S (First) = '.' then
            Error := False;
            return;
         elsif I = 3
           or else S (First) not in Digit_10
           or else (I = 2 and then (V > 25 or else (V = 25 and then S (First) >= '6')))
         then
            Error := True;
            return;
         end if;
      end loop;
      raise Program_Error;
   end Parse_Byte_10;

   procedure Parse_IPV4 (S : String; V : out Unsigned_32; Error : out Boolean) is
      First : Integer := S'First;
      Byte  : Unsigned_8;
   begin
      V := 0;
      if S'Length = 0 then
        Error := True;
        return;
      end if;
      for I in 1 .. 4 loop
        Parse_Byte_10 (S, First, Byte, Error);
        exit when Error;
        V := Shift_Left (V, 8) or Unsigned_32 (Byte);
        if (First = S'Last + 1) /= (I = 4) then
           Error := True;
           exit;
        end if;
        exit when I = 4;
        First := First + 1;
      end loop;
   end Parse_IPV4;

   function Parse_IPV4 (S : String) return Unsigned_32 is
      V     : Unsigned_32 := 0;
      First : Integer := S'First;
      Byte  : Unsigned_8;
      Error : Boolean;
   begin
      for I in 1 .. 4 loop
        Parse_Byte_10 (S, First, Byte, Error);
        pragma Assert (not Error);
        V := Shift_Left (V, 8) or Unsigned_32 (Byte);
        exit when I = 4;
        First := First + 1;
      end loop;
      return V;
   end Parse_IPV4;

   --------------------------------
   -- Printing of IPV4 Addresses --
   --------------------------------

   --  The string is constructed in one pass, starting from the end

   --  S is the smallest possible string presenting V (no leading zeros)
   function Is_Smallest_Byte_10 (S : String; V : Unsigned_8) return Boolean is
     (S'Length = (if V >= 100 then 3 elsif V >= 10 then 2 else 1)
      and then S (S'Last) = Char_Of_Byte_10 (V rem 10)
      and then (if V >= 10 then S (S'Last - 1) = Char_Of_Byte_10 ((V / 10) rem 10))
      and then (if V >= 100 then S (S'First) = Char_Of_Byte_10 (V / 100)))
   with Ghost;

   --  Print the Unsigned_8 V in S so that it ends at Last. Last is modified to
   --  designate the index preceding the printed value.
   procedure Print_Byte_10 (V : Unsigned_8; S : in out String; Last : in out Natural) with
   --  Tell GNATprove that S might not be entirely initialized on subprogram entry/exit
     Relaxed_Initialization => S,
     Pre  => S'Last < Integer'Last and then Last in s'Range and then Last - 2 >= s'First,
     Post => Last in s'First - 1 .. Last'Old and then Last'Old - Last <= 3
     and then S (Last + 1 .. Last'Old)'Initialized
     and then Is_Smallest_Byte_10 (S (Last + 1 .. Last'Old), V)
     and then (for all K in s'Range =>
                 (if K not in Last + 1 .. Last'Old then S (K)'Initialized = S'Old (K)'Initialized))
     and then (for all K in s'Range =>
                 (if K not in Last + 1 .. Last'Old and S (K)'Initialized then S (K) = S'Old (K)))
   is
      W : Unsigned_8 := V;
   begin
      for I in 1 .. 3 loop
        S (Last) := Char_Of_Byte_10 (W rem 10);
        Last := Last - 1;
        W := W / 10;
        exit when W = 0;
      end loop;
   end Print_Byte_10;

   function Print_IPV4 (V : Unsigned_32) return String is

      --  Proof that S represents V at the end of the subprogram
      procedure Prove_Is_IPV4 (S : String; D1, D2, D3 : Positive; V : Unsigned_32) with
        Ghost,
        Pre => S'Last < Integer'Last and then S'Length > 0
          and then D1 in S'First .. S'Last and then D2 in D1 + 1 .. S'Last and then D3 in D2 + 1 .. S'Last
          and then S (D1) = '.' and then S (D2) = '.' and then S (D3) = '.'
          and then Is_Smallest_Byte_10 (S (S'First .. D1 - 1), Unsigned_8 (Shift_Right (V, 24)))
          and then Is_Smallest_Byte_10 (S (D1 + 1 .. D2 - 1), Unsigned_8 (Shift_Right (V, 16) and 16#FF#))
          and then Is_Smallest_Byte_10 (S (D2 + 1 .. D3 - 1), Unsigned_8 (Shift_Right (V, 8) and 16#FF#))
          and then Is_Smallest_Byte_10 (S (D3 + 1 .. S'Last), Unsigned_8 (V and 16#FF#)),
        Post => Valid_IPV4 (S) and then Is_IPV4 (S, V);
      procedure Prove_Is_IPV4 (S : String; D1, D2, D3 : Positive; V : Unsigned_32) is
      begin
        pragma Assert (D1 = Find_First_Dot (S, S'First));
        pragma Assert (D2 = Find_First_Dot (S, D1 + 1));
        pragma Assert (D3 = Find_First_Dot (S, D2 + 1));
        pragma Assert (Is_Byte_10 (S, S'First, D1 - 1, Unsigned_8 (Shift_Right (V, 24))));
        pragma Assert (Is_Byte_10 (S, D1 + 1, D2 - 1, Unsigned_8 (Shift_Right (V, 16) and 16#FF#)));
        pragma Assert (Is_Byte_10 (S, D2 + 1, D3 - 1, Unsigned_8 (Shift_Right (V, 8) and 16#FF#)));
        pragma Assert (Is_Byte_10 (S, D3 + 1, S'Last, Unsigned_8 (V and 16#FF#)));
      end Prove_Is_IPV4;

      subtype Small_String is String (1 .. 15);
      S    : Small_String with Relaxed_Initialization;
      --  Tell GNATprove that S might not be entirely initialized before an element is read
      Last : Natural := 15;
      W    : Unsigned_32 := V;

      Ds : array (1 .. 3) of Positive with Ghost, Relaxed_Initialization;
      --  Ghost array to store the positions of the dots
   begin
      for I in 1 .. 4 loop
        Print_Byte_10 (Unsigned_8 (W and 16#FF#), S, Last);
        exit when I = 4;

        Ds (I) := Last;

        S (Last) := '.';
        Last := Last - 1;
        W := Shift_Right (W, 8);
      end loop;

      declare
        Lst : constant Positive := 15 - Last;
        Res : String (1 .. Lst) := S (Last + 1 .. 15);
      begin
        Prove_Is_IPV4 (Res, Ds (3) - Last, Ds (2) - Last, Ds (1) - Last, V);
        return Res;
      end;
   end Print_IPV4;

begin
  null;
end;
