package body IPV6_Parsing with SPARK_Mode is

   --------------------------------------------
   -- Body of the Specification-Only Queries --
   --------------------------------------------

   function Find_First_Colon (S : String; First : Integer) return Integer is
   begin
      for I in First .. s'Last loop
         if S (I) = ':' then
            return I;
         end if;
         pragma Loop_Invariant (for all K in First .. I => S (K) /= ':');
      end loop;
      return s'Last + 1;
   end Find_First_Colon;

   function Find_Last_Colon (S : String; Last : Integer) return Integer is
   begin
      for I in reverse s'First .. Last loop
         if S (I) = ':' then
            return I;
         end if;
         pragma Loop_Invariant (for all K in I .. Last => S (K) /= ':');
      end loop;
      return s'First - 1;
   end Find_Last_Colon;

   function Find_Double_Colon (S : String; First : Positive) return Integer is
   begin
      for I in First .. S'Last - 1 loop
         if S (I) = ':' and S (I + 1) = ':' then
            return I;
         end if;
         pragma Loop_Invariant (for all K in First .. I => not Is_Double_Colon (S, K));
      end loop;
      return S'Last + 1;
   end Find_Double_Colon;

   ------------------------------------
   -- Proof of  Lemma_Is_IPV6_Unique --
   ------------------------------------

   procedure Lemma_Is_Halfword_Unique (S : String; First, Last : Integer; V1, V2 : Unsigned_16) with
     Ghost,
     Pre => First in s'Range and then Last in s'Range
     and then Is_Halfword (s, First, Last, V1) and then Is_Halfword (s, First, Last, V2),
     Post => V1 = V2;
   procedure Lemma_Is_Halfword_Unique (S : String; First, Last : Integer; V1, V2 : Unsigned_16) is null;

   procedure Lemma_Is_Value_Unique (S : String; First, Last : Integer; V1, V2 : Unsigned_128) with
     Ghost,
     Pre => S'Last < Integer'Last and then First in s'Range
     and then Last in s'Range and then First <= Last
     and then (Last = S'Last or else S (Last + 1) = ':')
     and then Is_Value (s, V1, First, Last) and then Is_Value (s, V2, First, Last),
     Post => V1 = V2,
     Subprogram_Variant => (Decreases => Last);
   procedure Lemma_Is_Value_Unique (S : String; First, Last : Integer; V1, V2 : Unsigned_128) is
     C : constant Natural := Find_Last_Colon (S, Last);
   begin
     Lemma_Is_Halfword_Unique (S, C + 1, Last, Unsigned_16 (V1 and 16#FFFF#), Unsigned_16 (V2 and 16#FFFF#));
     if C > First then
        Lemma_Is_Value_Unique (S, First, C - 1, Shift_Right (V1, 16), Shift_Right (V2, 16));
     end if;
   end Lemma_Is_Value_Unique;

   procedure Lemma_Is_IPV6_Unique (N : Natural; V1, V2 : Unsigned_128) with
     Ghost,
     Pre => N in 0 .. 8
     and then Shift_Right_16 (V1, 8 - N) = Shift_Right_16 (V2, 8 - N)
     and then (V1 and Mask (8 - N)) = (V2 and Mask (8 - N)),
     Post => V1 = V2;
   procedure Lemma_Is_IPV6_Unique (N : Natural; V1, V2 : Unsigned_128) is null;

   procedure Lemma_Is_IPV6_Unique (S : String; V1, V2 : Unsigned_128) is
     CC  : constant Positive := Find_Double_Colon (S, S'First);
   begin
     if CC = S'Last + 1 then
       Lemma_Is_Value_Unique (S, S'First, S'Last, V1, V2);
     else
       declare
         N     : constant Natural := (if CC = S'First then 0 else 1 + Number_Of_Colons (S, S'First, CC - 1));
         Head1 : constant Unsigned_128 := Shift_Right_16 (V1, 8 - N);
         Tail1 : constant Unsigned_128 := V1 and Mask (8 - N);
         Head2 : constant Unsigned_128 := Shift_Right_16 (V2, 8 - N);
         Tail2 : constant Unsigned_128 := V2 and Mask (8 - N);
       begin
         if S (S'First) /= ':' then
           Lemma_Is_Value_Unique (S, S'First, CC - 1, Head1, Head2);
         end if;
         if S (S'Last) /= ':' then
           Lemma_Is_Value_Unique (S, CC + 2, S'Last, Tail1, Tail2);
         end if;
         Lemma_Is_IPV6_Unique (N, V1, V2);
       end;
     end if;
   end Lemma_Is_IPV6_Unique;

   -------------------------------
   -- Parsing of IPV6 Addresses --
   -------------------------------

   --  The string is parsed in one pass

   function Char_Of_Byte_16 (i : Small_Halfword) return Digit_16 is
     (case i is
         when 0 => '0',
         when 1 => '1',
         when 2 => '2',
         when 3 => '3',
         when 4 => '4',
         when 5 => '5',
         when 6 => '6',
         when 7 => '7',
         when 8 => '8',
         when 9 => '9',
         when 10 => 'a',
         when 11 => 'b',
         when 12 => 'c',
         when 13 => 'd',
         when 14 => 'e',
         when 15 => 'f');

   --  Parse the slice of S between First and the first colon if any (the end of
   --  S otherwise) as an Unsigned_16 in base 16. Error is set to False iff this
   --  slice is a valid Unsigned_16. In this case, V is set to this number and
   --  First is modified to designate the first colon in S.
   procedure Parse_Halfword (S : String; First : in out Positive; V : out Unsigned_16; Error : out Boolean) with
     Pre  => s'Last < Integer'Last and then First in s'First .. s'Last + 1,
     Post => First in First'Old .. s'Last + 1 and then First - First'Old <= 4
     and then Error = not Valid_Halfword (S, First'Old, Find_First_Colon (S, First'Old) - 1)
     and then (if not Error then First = Find_First_Colon (S, First'Old) and then Is_Halfword (S, First'Old, First - 1, V));

   procedure Parse_Halfword (S : String; First : in out Positive; V : out Unsigned_16; Error : out Boolean) is
      First_Old : Positive := First with Ghost;
   begin
      V := 0;
      if First > S'Last or else S (First) not in Digit_16 then
         Error := True;
         return;
      end if;

      --  The small loop with no invariants is unrolled for proof
      for I in 1 .. 4 loop
         V := V * 16 + Byte_Of_Char_16 (S (First));
         First := First + 1;

         if First > S'Last or else S (First) = ':' then
            Error := False;
            pragma Assert (Valid_Halfword (S, First_Old, First - 1));
            return;
         elsif I = 4 or else S (First) not in Digit_16 then
            Error := True;
            return;
         end if;
      end loop;
      raise Program_Error;
   end Parse_Halfword;

   procedure Parse_IPV6 (S : String; Error : out Boolean; V : out Unsigned_128) is
      CC_Seen : Boolean := False;
      --  Whether the double colon has been encountered yet
      Head    : Unsigned_128 := 0;
      --  The IP address computed up to the double colon
      Tail    : Unsigned_128 := 0;
      --  The IP address computed after to the double colon

      First   : Integer := S'First;

      N       : Positive := 1 with Ghost;
      --  Iteration iteration corresponding to the double colon when it is found
      CC      : constant Natural :=
        (if S'Length > 0 then Find_Double_Colon (S, S'First) else 0) with Ghost;
      --  Position of the double colon

      --  Iterate through the remaining of the string once the search is over to
      --  prove that it cannot represent a valid IPV6 address. We already
      --  know at this point that we have too many halfwords. However, as the
      --  validity predicate counts the colons until the end of the string,
      --  we need to continue the iteration to convice the proof tool that the
      --  number of colons will only increase from here.
      --  The procedure has no contracts, so GNATprove will inline it at the
      --  point of call.

      procedure Prove_Invalid_IP_ACCress with Ghost is
      begin
        if not Error and then First /= S'Last + 1 then
           declare
             F : Positive := First;

           begin
             --  Iterate through the remaining of the string by going from colon
             --  to colon. We don't care about the characters in between.

             while F < S'Last + 1 loop
               declare
                 C : constant Positive := Find_First_Colon (S, F);

               begin
                 pragma Assert (if C = S'Last + 1 then Find_Last_Colon (S, S'Last) = F - 1);
                 exit when C = S'Last + 1;
                 pragma Assert (Find_Last_Colon (S, C - 1) = F - 1);

                 --  If the double colon had not been seen before we enter this
                 --  loop, then we are interested here in the number of halfwords
                 --  before the double colon. We stop when the double colon is
                 --  reached.

                 if not CC_Seen and then F = C then
                   pragma Assert (Is_Double_Colon (S, C - 1));
                   pragma Assert (C - 1 = CC);
                   pragma Assert (Number_Of_Colons (S, S'First, F - 2) > 6);
                   exit;
                 end if;
                 F := C + 1;
               end;
               pragma Loop_Variant (Increases => F);
               pragma Loop_Invariant (S (F - 1) = ':');
               pragma Loop_Invariant (F in F'Loop_Entry + 1 .. S'Last + 1);
               pragma Loop_Invariant (if not CC_Seen then (for all K in S'First .. F - 2 => not Is_Double_Colon (S, K)));
               pragma Loop_Invariant (if not CC_Seen then Number_Of_Colons (S, S'First, F - 2) > 7);
               pragma Loop_Invariant (if CC_Seen then Number_Of_Colons (S, CC + 2, F - 2) > 7 - N);
             end loop;
           end;
           pragma Assert_And_Cut (not Valid_IPV6 (S));
        end if;
      end Prove_Invalid_IP_ACCress;
   begin
      V := 0;

      --  If S is empty, it is not a valid representation of an IPV6 address

      if S'Length = 0 then
         Error := True;
         return;

      --  If the first character of S is a colon, it should be a double colon

      elsif S (First) = ':' then
         if First < S'Last and then S (First + 1) /= ':' then
           Error := True;
           return;
         end if;

         --  Skip the first colon

         First := First + 1;
      end if;

      --  The following loop assumes that we start either at the beginning of S
      --  or just after a colon and tries 8 times to read either a colon (to
      --  find the double colon) or a halfword. For each halfword read preceding
      --  the double colon (if any), Head is shifted to the left and updated
      --  with the value read. Once the double colon has been seen, it is Tail
      --  which is updated with the read halfword, but Head is still shifted
      --  to the left. When we reach the end of the string, we still shift left
      --  by the remaining number of iterations to stand for the elided zeros.

      for I in 1 .. 8 loop

         --  No matter what, we shift Head to the left

         Head := Shift_Left (Head, 16);

         --  If we have reached the end of S, we should have seen the double
         --  colon or we are missing an halfword.

         if First > S'Last then
            Error := not CC_Seen;
            pragma Assert (if Error then not Valid_IPV6 (S));
            exit when Error;

         --  We have found a double colon. If we had already found one before,
         --  the address is invalid. Update N and CC_Seen and got to the next
         --  character of S.

         elsif S (First) = ':' then
            pragma Assert (Is_Double_Colon (S, First - 1));
            Error := CC_Seen;
            pragma Assert (if Error then not Valid_IPV6 (S));
            exit when Error;
            pragma Assert (First - 1 = Find_Double_Colon (S, S'First));
            N := I;
            CC_Seen := True;
            First := First + 1;

         --  Otherwise, try to read an halfword from S

         else
            declare
               Halfword : Unsigned_16;
               Previous : constant Integer := First with Ghost;
            begin
               Parse_Halfword (S, First, Halfword, Error);
               pragma Assert (if Error then not Valid_IPV6 (S));
               exit when Error;
               pragma Assert (Find_Last_Colon (S, First - 1) = Previous - 1);

               --  If we have seen the double colon already, shift tail to the
               --  left and update it with the value read.

               if CC_Seen then
                  Tail := Shift_Left (Tail, 16) or Unsigned_128 (Halfword);
                  pragma Assert (Is_Value (S, Tail, CC + 2, First - 1));
                  pragma Assert (if S (S'First) /= ':' then Is_Value (S, Shift_Right_16 (Head, I - N + 1), S'First, CC - 1));
                  pragma Assert (Number_Of_Colons (S, CC + 2, First - 1) = I - N - 1);

               --  Otherwise, update Head with the value read

               else
                  Head := Head or Unsigned_128 (Halfword);
                  pragma Assert (Is_Value (S, Head, S'First, First - 1));
               end if;
            end;

            --  If after the read, we have found a colon at the end of S, the
            --  string is not a valid address, or the last colon would have been
            --  a double colon.

            if First = S'Last then
              Error := True;
              pragma Assert (not Valid_IPV6 (S));
              exit;

            --  Skip the last colon read if any

            elsif First /= S'Last + 1 then
              First := First + 1;
               pragma Assert (S (First - 1) = ':');
            end if;
         end if;

         pragma Loop_Invariant (First in First'Loop_Entry + 1 .. S'Last + 1);

         --  We are jumping from a colon to the next, so the last character read is always a colon
         pragma Loop_Invariant (First > S'Last or else S (First - 1) = ':');
         --  CC_Seen is true iff the double colon has been processed already
         pragma Loop_Invariant (CC_Seen = (CC < First - 1));
         --  The double colon was found in the current iteration iff it is located just before the last character read
         pragma Loop_Invariant (if CC_Seen and then First <= S'Last then (I = N) = (First - 2 = CC));
         --  If the double colon was seen then N is set to something before I
         pragma Loop_Invariant (if CC_Seen then N <= I);

         --  The loop would have ended if S was found to be ill-formed. State that up until First,
         --  S is known to be a valid representation of an IPV6 address.
         --  If we have reached the end of the string and found a colon there, it was a double colon
         pragma Loop_Invariant (if First > S'Last and then S (S'Last) = ':' then CC_Seen and Is_Double_Colon (S, S'Last - 1));
         --  The double colon was found in the first iteration iff the first element of S is a colon
         pragma Loop_Invariant ((S (S'First) = ':') = (CC_Seen and then N = 1));
         --  If we have found a double colon, we have not found another one yet
         pragma Loop_Invariant (if CC_Seen then Find_Double_Colon (S, CC + 1) >= First - 1);

         --  If we have not seen a double colon, we have read I halfwords so far, so we have found I - 1 colons before the last one
         pragma Loop_Invariant (if First = S'Last + 1 and then not CC_Seen then Number_Of_Colons (S, S'First, S'Last) = I - 1);
         pragma Loop_Invariant (if First <= S'Last and then not CC_Seen then Number_Of_Colons (S, S'First, First - 2) = I - 1);
         --  If we have seen the double colon, N - 1 is the number of halfwords read before the double colon
         pragma Loop_Invariant (if CC_Seen then Number_Of_Colons (S, S'First, CC - 1) = Integer'Max (0, N - 2));
         --  If we have seen a double colon at iteration N, we have read I - N halfwords since, so we have found I - N - 1 colons before the last one
         pragma Loop_Invariant (if First = S'Last + 1 and then CC_Seen and then S (S'Last) /= ':' then Number_Of_Colons (S, CC + 2, S'Last) <= I - N - 1);
         pragma Loop_Invariant (if First <= S'Last and then CC_Seen and then CC < First - 2 then Number_Of_Colons (S, CC + 2, First - 2) = I - N - 1);

         --  If the double colon is located at the beginning of S, Head is 0
         pragma Loop_Invariant (if S (S'First) = ':' then Head = 0);
         --  If we have not seen a double colon, Head is the value read since the beginning of S
         pragma Loop_Invariant (if not CC_Seen and then First <= S'Last then First - 1 > S'First and then Is_Value (S, Head, S'First, First - 2));
         pragma Loop_Invariant (if not CC_Seen and then First = S'Last + 1 then Is_Value (S, Head, S'First, S'Last));
         --  If we have seen the double colon and it is not at the beginning, Head is the number read before CC
         pragma Loop_Invariant (if CC_Seen and then S (S'First) /= ':' then Is_Value (S, Shift_Right_16 (Head, I - N + 1), S'First, CC - 1));
         --  If we have not yet strictly after the double colon or if the double colon is at then end, then Tail is 0
         pragma Loop_Invariant (if not CC_Seen or I = N or S'Last - 1 = CC then Tail = 0);
         --  If we have seen a double colon, Tail is the number read afterward
         pragma Loop_Invariant (if CC_Seen and then First <= S'Last and then I > N then Is_Value (S, Tail, CC + 2, First - 2));
         pragma Loop_Invariant (if CC_Seen and then First = S'Last + 1 and then S (S'Last) /= ':' then Is_Value (S, Tail, CC + 2, S'Last));

         --  Tail can be encoded in the number of halfwords read after N
         pragma Loop_Invariant (if CC_Seen then (Tail and Mask (I - N + 1)) = Tail);
         --  Head only has zeros in the range of Tail
         pragma Loop_Invariant (if CC_Seen then (Head and (not Mask (I - N + 1))) = Head);
         --  Head can be encoded in the number of halfwords read since the beginning of the iteration
         pragma Loop_Invariant ((Head and Mask (I)) = Head);

         --  Error is set to False
         pragma Loop_Invariant (not Error);
         --  We have only found valid halfwords until now
         pragma Loop_Invariant (if First <= S'Last then Valid_Halfwords (S, First) = Valid_Halfwords (S, S'First) else Valid_Halfwords (S, S'First));
      end loop;
      pragma Assert (if Error then not Valid_IPV6 (S));
      Prove_Invalid_IP_ACCress;
      Error := Error or else First /= S'Last + 1;
      pragma Assert (if not Error then Valid_IPV6 (S));

      --  If we have not found any error, Head or Tail is the IPV6 address encoded by S
      pragma Assert (if CC_Seen then Shift_Right_16 (Head or Tail, 9 - N) = Shift_Right_16 (Head, 9 - N));
      pragma Assert (if not Error and then CC_Seen then ((Head or Tail) and Mask (9 - N)) = Tail);
      pragma Assert (if not Error and then CC_Seen then Is_IPV6 (S, Head or Tail));
      V := Head or Tail;
   end Parse_IPV6;

   --------------------------------
   -- Printing of IPV4 Addresses --
   --------------------------------

   --  The string is constructed in one pass. We don't try to optimize the
   --  printing, so the resulting string is a sequence of 8 halfwords of exactly
   --  3 hexadecimal digits separated by a single colon.

   --  The slice S (First .. Last) is the simplest hexadecimal representation of
   --  the halfword V.
   function Is_Simplest_Halfword_Repr (S : String; First, Last : Integer; V : Unsigned_16) return Boolean is
     ((for all I in First .. Last => S (I) in Digit_16)
      and then V rem 16 = Byte_Of_Char_16 (S (Last))
      and then (V / 16) rem 16 = Byte_Of_Char_16 (S (First + 2))
      and then (V / 256) rem 16 =  Byte_Of_Char_16 (S (First + 1))
      and then V / 4096 = Byte_Of_Char_16 (S (First)))
   with Ghost,
     Pre  => First in s'Range and then Last in s'Range
     and then First = Last - 3;

   subtype String39 is String (1 .. 39);
   subtype One_To_Eight is Integer range 1 .. 8;

   --  S is the simplest representation of the IPV6 address V up to the Kth halfword
   function Is_Simplest_IPV6_Repr (V : Unsigned_128; S : String39; K : One_To_Eight) return Boolean is
      ((K <= 7 or else (Is_Simplest_Halfword_Repr (S, 1, 4, Unsigned_16 (Shift_Right (V, 112))) and then S (5) = ':'))
       and then (K <= 6 or else (Is_Simplest_Halfword_Repr (S, 6, 9, Unsigned_16 (Shift_Right (V, 96) and 16#FFFF#)) and then S (10) = ':'))
       and then (K <= 5 or else (Is_Simplest_Halfword_Repr (S, 11, 14, Unsigned_16 (Shift_Right (V, 80) and 16#FFFF#)) and then S (15) = ':'))
       and then (K <= 4 or else (Is_Simplest_Halfword_Repr (S, 16, 19, Unsigned_16 (Shift_Right (V, 64) and 16#FFFF#)) and then S (20) = ':'))
       and then (K <= 3 or else (Is_Simplest_Halfword_Repr (S, 21, 24, Unsigned_16 (Shift_Right (V, 48) and 16#FFFF#)) and then S (25) = ':'))
       and then (K <= 2 or else (Is_Simplest_Halfword_Repr (S, 26, 29, Unsigned_16 (Shift_Right (V, 32) and 16#FFFF#)) and then S (30) = ':'))
       and then (K <= 1 or else (Is_Simplest_Halfword_Repr (S, 31, 34, Unsigned_16 (Shift_Right (V, 16) and 16#FFFF#)) and then S (35 )= ':'))
       and then Is_Simplest_Halfword_Repr (S, 36, 39, Unsigned_16 (V and 16#FFFF#)))
   with Ghost;

   --  Lemma: The simplest representation of an IPV6 address is a valid representation
   procedure Lemma_Simplest_IPV6_Repr_Valid (V : Unsigned_128; S : String39) with
     Ghost,
     Pre  => Is_Simplest_IPV6_Repr (V, S, 8),
     Post => Valid_IPV6 (S) and then Is_IPV6 (S, V);
   procedure Lemma_Simplest_IPV6_Repr_Valid (V : Unsigned_128; S : String39) is
   begin
      --  S does not contain any double colons
      pragma Assert (Find_Double_Colon (S, S'First) = S'Last + 1);

      --  S is a sequence of halfwords separated by colons
      for I in 1 .. 8 loop
         pragma Assert (Valid_Halfword (S, (8 - I) * 5 + 1, (9 - I) * 5 - 1));
         pragma Assert (if I > 1 then Find_First_Colon (S, (8 - I) * 5 + 1) = (9 - I) * 5);
         pragma Loop_Invariant (Valid_Halfwords (S, (8 - I) * 5 + 1));
      end loop;

      --  S contains exactly 7 halfwords
      for I in 1 .. 8 loop
         pragma Assert (Find_Last_Colon (S, I * 5 - 1) = (I - 1) * 5);
         pragma Loop_Invariant (Number_Of_Colons (S, 1, I * 5 - 1) = I - 1);
      end loop;
      pragma Assert (Valid_IPV6 (S));

      --  S is the representation of V
      for I in 1 .. 8 loop
         pragma Assert (Find_Last_Colon (S, I * 5 - 1) = (I - 1) * 5);
         pragma Assert (Is_Simplest_Halfword_Repr (S, (I - 1) * 5 + 1, I * 5 - 1, Unsigned_16 (Shift_Right_16 (V, 8 - I) and 16#FFFF#)));
         pragma Assert (Is_Halfword (S, (I - 1) * 5 + 1, I * 5 - 1, Unsigned_16 (Shift_Right_16 (V, 8 - I) and 16#FFFF#)));
         pragma Loop_Invariant (Is_Value (S, Shift_Right_16 (V, 8 - I), 1, I * 5 - 1));
      end loop;
      pragma Assert (Is_IPV6 (S, V));
   end Lemma_Simplest_IPV6_Repr_Valid;

   procedure Print_Halfword (V : Unsigned_16; S : in out String; Last : in out Natural) with
     Pre  => S'Last < Integer'Last and then Last in s'Range and then Last - 3 >= s'First,
     Post => Last in s'First - 1 .. Last'Old and then Last'Old - Last = 4
     and then Is_Simplest_Halfword_Repr (S, Last + 1, Last'Old, V)
     and then (for all K in s'Range =>
                 (if K not in Last + 1 .. Last'Old then S (K) = S'Old (K)));

   procedure Print_Halfword (V : Unsigned_16; S : in out String; Last : in out Natural) is
      W : Unsigned_16 := V;
   begin
      --  The small loop with no invariants is unrolled for proof
      for I in 1 .. 4 loop
        S (Last) := Char_Of_Byte_16 (W rem 16);
        Last := Last - 1;
        W := W / 16;
      end loop;
      pragma Assert (Valid_Halfword (S, Last + 1, Last + 4));
   end Print_Halfword;

   function Print_IPV6 (V : Unsigned_128) return String is
      W     : Unsigned_128 := V;
      Last  : Integer := 39;
      Res   : String39 := (others => ' '); --useless initial value

   begin
      --  The small loop with no invariants is unrolled for proof
      for I in 1 .. 8 loop
         Print_Halfword (Unsigned_16 (W and 16#FFFF#), Res, Last);
         W := Shift_Right (W, 16);

         pragma Assert (Last = (8 - I) * 5);
         pragma Assert (W = Shift_Right_16 (V, I));

         exit when I = 8;
         Res (Last) := ':';
         Last := Last - 1;
      end loop;

      --  Check that Res really is the simplest representation of V
      pragma Assert (Is_Simplest_Halfword_Repr (Res, 36, 39, Unsigned_16 (V and 16#FFFF#)));
      pragma Assert (Is_Simplest_Halfword_Repr (Res, 31, 34, Unsigned_16 (Shift_Right (V, 16) and 16#FFFF#)));
      pragma Assert (Is_Simplest_Halfword_Repr (Res, 26, 29, Unsigned_16 (Shift_Right (V, 32) and 16#FFFF#)));
      pragma Assert (Is_Simplest_Halfword_Repr (Res, 21, 24, Unsigned_16 (Shift_Right (V, 48) and 16#FFFF#)));
      pragma Assert (Is_Simplest_Halfword_Repr (Res, 16, 19, Unsigned_16 (Shift_Right (V, 64) and 16#FFFF#)));
      pragma Assert (Is_Simplest_Halfword_Repr (Res, 11, 14, Unsigned_16 (Shift_Right (V, 80) and 16#FFFF#)));
      pragma Assert (Is_Simplest_Halfword_Repr (Res, 6, 9, Unsigned_16 (Shift_Right (V, 96) and 16#FFFF#)));

      --  Apply the lemma to deduce that Res is a valid representation of V
      Lemma_Simplest_IPV6_Repr_Valid (V, Res);
      return Res;
   end Print_IPV6;

begin
  null;
end;
