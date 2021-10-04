with Interfaces; use Interfaces;
package IPV6_Parsing with SPARK_Mode is
   subtype Digit_16 is Character with
     Static_Predicate => Digit_16 in '0' .. '9' | 'a' .. 'f' | 'A' .. 'F';
   subtype Small_Halfword is Unsigned_16 range 0 .. 15;

   function Byte_Of_Char_16 (c : Digit_16) return Small_Halfword is
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
         when '9' => 9,
         when 'a' => 10,
         when 'b' => 11,
         when 'c' => 12,
         when 'd' => 13,
         when 'e' => 14,
         when 'f' => 15,
         when 'A' => 10,
         when 'B' => 11,
         when 'C' => 12,
         when 'D' => 13,
         when 'E' => 14,
         when 'F' => 15);

   --------------------------------------------------
   -- Auxilliary Operations for Halfwords (16bits) --
   --------------------------------------------------

   --  Mask to get the leftmost I halfwords of a 128 bits integer
   function Mask (I : Natural) return Unsigned_128 is
     (case I is
         when 0      => 0,
         when 1      => 16#FFFF#,
         when 2      => 16#FFFF_FFFF#,
         when 3      => 16#FFFF_FFFF_FFFF#,
         when 4      => 16#FFFF_FFFF_FFFF_FFFF#,
         when 5      => 16#FFFF_FFFF_FFFF_FFFF_FFFF#,
         when 6      => 16#FFFF_FFFF_FFFF_FFFF_FFFF_FFFF#,
         when 7      => 16#FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF#,
         when 8      => 16#FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF#,
         when others => Raise Program_Error)
   with Ghost, Pre => I in 0 .. 8,
     Annotate => (GNATprove, Inline_For_Proof);

   --  Shift an unsigned 128 by I halfwords
   function Shift_Right_16 (V : Unsigned_128; I : Natural) return Unsigned_128 is
      (case I is
         when 8 => 0,
         when 7 => Shift_Right (V, 112),
         when 6 => Shift_Right (V, 96),
         when 5 => Shift_Right (V, 80),
         when 4 => Shift_Right (V, 64),
         when 3 => Shift_Right (V, 48),
         when 2 => Shift_Right (V, 32),
         when 1 => Shift_Right (V, 16),
         when 0 => V,
         when others => Raise Program_Error)
   with Ghost,
     Pre  => I in 0 .. 8,
     Annotate => (GNATprove, Inline_For_Proof);

   -------------------
   -- Specification --
   -------------------

   --  The slice S (First .. Last) represents a valid halfword in base 16
   function Valid_Halfword (S : String; First, Last : Integer) return Boolean is
     (First <= Last
      and then Last - First <= 3
      and then (for all I in First .. Last => s (I) in Digit_16))
   with Ghost,
     Pre => First > Last or else (First in s'Range and Last in s'Range);

   --  The slice S (First .. Last) represents V in base 16
   function Is_Halfword (S : String; First, Last : Integer; V : Unsigned_16) return Boolean is
     (Valid_Halfword (s, First, Last)
      and then First in Last - 3 .. Last
      and then V rem 16 = Byte_Of_Char_16 (S (Last))
      and then (V / 16) rem 16 = (if First < Last then Byte_Of_Char_16 (S (Last - 1)) else 0)
      and then (V / 256) rem 16 = (if First < Last - 1 then Byte_Of_Char_16 (S (Last - 2)) else 0)
      and then V / 4096 = (if First < Last - 2 then Byte_Of_Char_16 (S (Last - 3)) else 0))
   with Ghost,
     Pre  => First in s'Range and then Last in s'Range;

   --  Return the first colon following First in S if any and S'Last + 1 otherwise
   function Find_First_Colon (S : String; First : Integer) return Integer with
     Ghost,
     Pre => s'Last < Integer'Last and then First in s'First .. s'Last + 1,
     Post => Find_First_Colon'Result in First .. s'Last + 1
     and then (if Find_First_Colon'Result in s'Range then S (Find_First_Colon'Result) = ':')
     and then (for all K in First .. Find_First_Colon'Result - 1 => S (K) /= ':');

   --  Return the last colon before Last in S if any and S'First - 1 otherwise
   function Find_Last_Colon (S : String; Last : Integer) return Integer with
     Ghost,
     Pre => s'Last < Integer'Last and then Last in s'First - 1 .. s'Last,
     Post => Find_Last_Colon'Result in s'First - 1 .. Last
     and then (if Find_Last_Colon'Result in S'Range then S (Find_Last_Colon'Result) = ':')
     and then (for all K in Find_Last_Colon'Result + 1 .. Last => S (K) /= ':');

   --  S has 2 colons in a row at position P
   function Is_Double_Colon (S : String; P : Positive) return Boolean is
     (P < S'Last and then S (P) = ':' and then S (P + 1) = ':')
   with Ghost,
     Pre => P in S'Range;

   --  Find the first occurrence of a double colon in S starting at First
   function Find_Double_Colon (S : String; First : Positive) return Integer with
     Ghost,
     Pre  => First in S'Range and then S'Last < Integer'Last,
     Post => Find_Double_Colon'Result in First .. S'Last + 1
     and then (if Find_Double_Colon'Result in S'Range then
                 Is_Double_Colon (S, Find_Double_Colon'Result))
     and then (for all K in First .. Find_Double_Colon'Result - 1 =>
                 not Is_Double_Colon (S, K));

   --  Recursively count the number of colons in S between First and Last
   function Number_Of_Colons (S : String; First, Last : Integer) return Natural with
     Ghost,
     Pre  => S'Last < Integer'Last and then First in S'Range
     and then Last in First - 1 .. S'Last,
     Post => Number_Of_Colons'Result <= Last - First + 1,
     Subprogram_Variant => (Decreases => Last);

   function Number_Of_Colons (S : String; First, Last : Integer) return Natural is
     (declare
        C : constant Natural := Find_Last_Colon (S, Last);
      begin
        (if C < First then 0 else Number_Of_Colons (S, First, C - 1) + 1));

   --  The suffix of S starting at First is a sequence of halfwords separated by one or several colons
   function Valid_Halfwords (S : String; First : Positive) return Boolean with
     Ghost,
     Pre => S'Last < Integer'Last and then First in S'Range,
     Subprogram_Variant => (Increases => First);

   function Valid_Halfwords (S : String; First : Positive) return Boolean is
     (declare
        C : constant Positive := Find_First_Colon (S, First);
      begin
        (if C = First then C = S'Last or else Valid_Halfwords (S, First + 1)
         else Valid_Halfword (S, First, C - 1)
              and then (C >= S'Last or else Valid_Halfwords (S, C + 1))));

   --  S is a valid IPV6 address:
   --    * It is a sequence of valid halfwords separated by colons
   --    * It contains at most one occurrence of a double colon
   --    * It starts/ends by a digit or the double colon
   --    * It contains exactly 8 halfwords if it has no double colon, 7 at most otherwise.
   function Valid_IPV6 (S : String) return Boolean is
     (S'Length > 0 and then (if S (S'First) = ':' then Is_Double_Colon (S, S'First))
      and then (if S (S'Last) = ':' then Is_Double_Colon (S, S'Last - 1))
      and then Valid_Halfwords (S, S'First)
      and then
        (declare
           CC : constant Natural := Find_Double_Colon (S, S'First);
         begin
           (if CC = S'Last + 1 then Number_Of_Colons (S, S'First, S'Last) = 7
            else Find_Double_Colon (S, CC + 1) = S'Last + 1
              and then
                (if S (S'First) = ':' then (S'Length = 2 or else Number_Of_Colons (S, CC + 2, S'Last) <= 6)
                 elsif S (S'Last) = ':' then Number_Of_Colons (S, S'First, CC - 1) <= 6
                 else Number_Of_Colons (S, S'First, CC - 1) + Number_Of_Colons (S, CC + 2, S'Last) <= 5))))
   with Ghost,
     Pre => S'Last < Integer'Last;

   --  The slice S (First .. Last) is a sequence of halfwords separated by a single colon representing the number V
   function Is_Value (S : String; V : Unsigned_128; First, Last : Integer) return Boolean with
     Ghost,
     Pre => S'Last < Integer'Last and then Last in S'Range
     and then First in S'Range and then First <= Last,
     Subprogram_Variant => (Decreases => Last);

   function Is_Value (S : String; V : Unsigned_128; First, Last : Integer) return Boolean is
     (declare
        C : constant Natural := Find_Last_Colon (S, Last);
      begin
        (C < Last
         and then Is_Halfword (S, C + 1, Last, Unsigned_16 (V and 16#FFFF#))
         and then (if C <= First then Shift_Right (V, 16) = 0
                   else Is_Value (S, Shift_Right (V, 16), First, C - 1))));

   --  S represents the IPV6 address V:
   --    * If S contains no double colons, then S is a sequence of halfwords
   --      separated by a single colon representing the number V.
   --    * Otherwise, S is made of two single-colon-separated sequences of
   --      halfwords with the double colons in the middle. If the first sequence
   --      holds N halfwords, then the first sequence represents the first
   --      16 * N bits of V while the second represents the rest.
   function Is_IPV6 (S : String; V : Unsigned_128) return Boolean is
     (declare
        CC : constant Positive := Find_Double_Colon (S, S'First);
      begin
        (if CC = S'Last + 1 then Is_Value (S, V, S'First, S'Last)
         else
           (declare
              N    : constant Natural := (if CC = S'First then 0 else 1 + Number_Of_Colons (S, S'First, CC - 1));
              Head : constant Unsigned_128 := Shift_Right_16 (V, 8 - N);
              Tail : constant Unsigned_128 := V and Mask (8 - N);
            begin (if S (S'First) /= ':' then Is_Value (S, Head, S'First, CC - 1) else Head = 0)
               and (if S (S'Last) /= ':' then Is_Value (S, Tail, CC + 2, S'Last) else Tail = 0))))
   with Ghost,
     Pre => S'Last < Integer'Last and then Valid_IPV6 (S);

   --  Lemma: Is_IPV6 defines uniquely an IPV6 address.
   --    This can be used to show that a call of parse after print indeed
   --    returns the input address.
   procedure Lemma_Is_IPV6_Unique (S : String; V1, V2 : Unsigned_128) with
     Ghost,
     Pre => S'Last < Integer'Last and then Valid_IPV6 (S)
     and then Is_IPV6 (S, V1) and then Is_IPV6 (S, V2),
     Post => V1 = V2;

   --------------------------------------------
   -- Parsing and Printing of IPV6 Addresses --
   --------------------------------------------

   --  Parse the string S. Error is set to False iff S represents a valid IPV6
   --  address. In this case, V is the value of this address.
   procedure Parse_IPV6 (S : String; Error : out Boolean; V : out Unsigned_128) with
     Pre  => s'Last < Integer'Last,
     Post => Error = not Valid_IPV6 (S)
       and then (if not Error then Is_IPV6 (S, V));

   --  Print V as a IPV6 address. We don't attend any fancy optimisation here,
   --  we just go for the simplest way of printing, where all the zeros are
   --  explicit.
   function Print_IPV6 (V : Unsigned_128) return String with
     Post => Print_IPV6'Result'First = 1 and then Print_IPV6'Result'Last = 39
     and then Valid_IPV6 (Print_IPV6'Result) and then Is_IPV6 (Print_IPV6'Result, V);

end IPV6_Parsing;
