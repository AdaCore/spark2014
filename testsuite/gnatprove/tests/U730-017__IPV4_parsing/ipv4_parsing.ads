with Interfaces; use Interfaces;
package IPV4_Parsing with SPARK_Mode is
   subtype Digit_10 is Character range '0' .. '9';
   subtype Small_Byte_10 is Unsigned_8 range 0 .. 9;

   function Char_Of_Byte_10 (i : Small_Byte_10) return Digit_10 is
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
         when 9 => '9');

   -------------------
   -- Specification --
   -------------------

   --  The slice S (First .. Last) of length 3 is less than "256"
   function Less_Than_Byte_Max_10 (S : String; First, Last : Positive) return Boolean is
     (S (First) < '2' or else
          (S (First) = '2' and then
             (S (First + 1) < '5'or else
                  (S (First + 1) = '5' and then S (First + 2) < '6'))))
   with Ghost,
     Pre => First = Last - 2 and then First in s'Range and then Last in s'Range;

   --  The slice S (First .. Last) represents a valid Unsigned_8 in base 10
   function Valid_Byte_10 (S : String; First, Last : Integer) return Boolean is
     (First <= Last
      and then Last - First <= 2
      and then (for all I in First .. Last => s (I) in Digit_10)
      and then (if Last - First = 2 then Less_Than_Byte_Max_10 (s, First, Last)))
   with Ghost,
     Pre => First > Last or else (First in s'Range and Last in s'Range);

   --  The slice S (First .. Last) represents V in base 10
   function Is_Byte_10 (S : String; First, Last : Integer; V : Unsigned_8) return Boolean is
     (First in Last - 2 .. Last
      and then Char_Of_Byte_10 (V rem 10) = S (Last)
      and then Char_Of_Byte_10 ((V / 10) rem 10) = (if First < Last then S (Last - 1) else '0')
      and then Char_Of_Byte_10 (V / 100) = (if First < Last - 1 then S (Last - 2) else '0'))
   with Ghost,
     Pre  => First in s'Range and then Last in s'Range,
     Post => (if Is_Byte_10'Result then Valid_Byte_10 (s, First, Last));

   --  Return the index of the first occurrence of a dot after First in S
   function Find_First_Dot (S : String; First : Integer) return Integer with
     Ghost,
     Pre => s'Last < Integer'Last and then First in s'First .. s'Last + 1,
     Post => Find_First_Dot'Result in First .. s'Last + 1
     and then (if Find_First_Dot'Result in s'Range then S (Find_First_Dot'Result) = '.')
     and then (for all K in First .. Find_First_Dot'Result - 1 => S (K) /= '.');

   --  S is a valid IPV4 address: It is made of 4 parts speparated by dots,
   --  each part representing an Unsigned_8.
   function Valid_IPV4 (S : String) return Boolean is
     (S'Length > 0 and then
        (declare
           D1 : constant Positive := Find_First_Dot (S, S'First);
           D2 : constant Positive :=
           (if D1 = S'Last + 1 then S'Last + 1 else Find_First_Dot (S, D1 + 1));
           D3 : constant Positive :=
           (if D2 = S'Last + 1 then S'Last + 1 else Find_First_Dot (S, D2 + 1));
         begin
           D1 <= s'Last and then Valid_Byte_10 (S, S'First, D1 - 1)
           and then D2 <= s'Last and then Valid_Byte_10 (S, D1 + 1, D2 - 1)
           and then D3 <= s'Last and then Valid_Byte_10 (S, D2 + 1, D3 - 1)
           and then Valid_Byte_10 (S, D3 + 1, S'Last)))
   with Ghost,
     Pre => s'Last < Integer'Last;

   --  S is an IPV4 address encoding the value V
   function Is_IPV4 (S : String; V : Unsigned_32) return Boolean is
     (declare
        D1 : constant Positive := Find_First_Dot (S, S'First);
        D2 : constant Positive := Find_First_Dot (S, D1 + 1);
        D3 : constant Positive := Find_First_Dot (S, D2 + 1);
      begin
        Is_Byte_10 (S, S'First, D1 - 1, Unsigned_8 (Shift_Right (V, 24)))
        and then Is_Byte_10 (S, D1 + 1, D2 - 1, Unsigned_8 (Shift_Right (V, 16) and 16#FF#))
        and then Is_Byte_10 (S, D2 + 1, D3 - 1, Unsigned_8 (Shift_Right (V, 8) and 16#FF#))
        and then Is_Byte_10 (S, D3 + 1, S'Last, Unsigned_8 (V and 16#FF#)))
   with Ghost,
     Pre => s'Last < Integer'Last and then Valid_IPV4 (S);

   --  Lemma: Is_IPV4 defines uniquely an IPV4 address.
   --    This can be used to show that a call of parse after print indeed
   --    returns the input address.
   procedure Lemma_Is_IPV4_Unique (S : String; V1, V2 : Unsigned_32) with
     Ghost,
     Pre => s'Last < Integer'Last and then Valid_IPV4 (S)
     and then Is_IPV4 (s, V1) and then Is_IPV4 (s, V2),
     Post => V1 = V2;

   --------------------------------------------
   -- Parsing and Printing of IPV4 Addresses --
   --------------------------------------------

   --  Parse the string S. Error is set to False iff S represents a valid IPV4
   --  address. In this case, V is the value of this address.
   procedure Parse_IPV4 (S : String; V : out Unsigned_32; Error : out Boolean) with
     Pre  => s'Last < Integer'Last,
     Post => Error = not Valid_IPV4 (S)
     and then (if not Error then Is_IPV4 (S, V));

   --  Parse the string S knowing that it represents a valid IPV4 address.
   --  Return the value of this address.
   function Parse_IPV4 (S : String) return Unsigned_32 with
     Pre  => s'Last < Integer'Last and then Valid_IPV4 (S),
     Post => Is_IPV4 (S, Parse_IPV4'Result);

   --  Print V as a IPV4 address
   function Print_IPV4 (V : Unsigned_32) return String with
     Post => Print_IPV4'Result'First = 1
     and then Print_IPV4'Result'Length <= 15
     and then Valid_IPV4 (Print_IPV4'Result)
     and then Is_IPV4 (Print_IPV4'Result, V);

end IPV4_Parsing;
