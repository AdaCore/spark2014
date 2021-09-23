--  Last entirely proved on 2021-07-30 with level 3.
--  Unrolling is necessary to prove this code, but we disable it in the
--  testsuite to make the test shorter.

with Interfaces; use Interfaces;

package Integer32_Parsing with SPARK_Mode is

   function Valid_Int (s: string) return Boolean with
     Ghost,
     Pre => s'Last < Integer'Last,
     Post =>
       (if Valid_Int'Result then s'Length > 0 and then s(s'First) in '-' | '0' .. '9'
        and then (for all i in s'First + 1 .. s'Last => s (i) in '0' .. '9'));

   function Valid_Int_32 (s: string) return Boolean with
     Ghost,
     Pre => s'Last < Integer'Last,
     Post => (if Valid_Int_32'Result then Valid_Int (s));

   function Is_Integer_32 (s: string; V : Integer_32) return Boolean with
     Ghost,
     Pre => s'Last < Integer'Last and then Valid_Int (s);

   procedure Lemma_Integer_Rep_Unique (s : string; V1, V2 : Integer_32) with
     Ghost,
     Pre => s'Last < Integer'Last and then Valid_Int (s)
     and then Is_Integer_32 (s, V1) and then Is_Integer_32 (s, V2),
     Post => V1 = V2;

   procedure Lemma_Is_Valid_Extensional (s1, s2 : string) with
     Ghost,
     Pre => s1'Last < Integer'Last and then s2'Last < Integer'Last
     and then Valid_Int_32 (s1) and then s1 = s2,
     Post => Valid_Int_32 (s2);

   procedure Lemma_Is_Integer_Extensional (s1, s2 : string; V : Integer_32) with
     Ghost,
     Pre => s1'Last < Integer'Last and then s2'Last < Integer'Last
     and then Valid_Int (s1) and then s1 = s2 and then Is_Integer_32 (s1, V),
     Post => Valid_Int (s2) and then Is_Integer_32 (s2, V);

   function Parse_Int_32 (s: string) return Integer_32 with
     Pre => s'Last < Integer'Last and then Valid_Int_32 (s),
     Post => Is_Integer_32 (s, Parse_Int_32'Result);

   procedure Parse_Int_32 (s: string; V : out Integer_32; error : out Boolean) with
     Pre => s'Last < Integer'Last,
     Post => error = not Valid_Int_32 (s)
       and then (if not error then Is_Integer_32 (s, V));

   function Length (V : Integer_32) return Positive is
     ((if V < 0 then 1 else 0) +
        (if V in -9 .. 9 then 1
         elsif V in -99 .. 99 then 2
         elsif V in -999 .. 999 then 3
         elsif V in -9_999 .. 9_999 then 4
         elsif V in -99_999 .. 99_999 then 5
         elsif V in -999_999 .. 999_999 then 6
         elsif V in -9_999_999 .. 9_999_999 then 7
         elsif V in -99_999_999 .. 99_999_999 then 8
         elsif V in -999_999_999 .. 999_999_999 then 9
         else 10));

   function Print_Int_32 (V: Integer_32) return string with
     Post => Print_Int_32'Result'Length = Length (V)
     and then Print_Int_32'Result'First = 1
     and then Valid_Int_32 (Print_Int_32'Result)
     and then Is_Integer_32 (Print_Int_32'Result, V);

end Integer32_Parsing;
