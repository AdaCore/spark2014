-- MB27-015 - Implementation of LRM 4.2(2)
--
-- Test cases for constraints that reference variables
package P
  with SPARK_Mode => On
is
   -- TU: 1. A ``constraint``, excluding the ``range`` of a
   -- ``loop_parameter_specification``, shall not be defined using an
   -- expression with a variable input.

   A : Integer := 1;
   B : Integer := 10;

   C1  : constant Integer := 1;
   C10 : constant Integer := 10;

   N1  : constant := 1;

   -- Subtype declarations using literals, named numbers
   -- and variables
   subtype S1 is Integer range 1 .. 10;   -- legal
   subtype S2 is Integer range N1 .. C10; -- legal
   subtype S3 is Integer range 1 .. B;    -- illegal
   subtype S4 is Integer range A .. 10;   -- illegal
   subtype S5 is Integer range A .. B;    -- illegal

   -- Same but using explicit constants
   CA : constant Integer := A;
   CB : constant Integer := B;
   subtype S6 is Integer range 1 .. CB;  -- legal
   subtype S7 is Integer range CA .. 10; -- legal
   subtype S8 is Integer range CA .. CB; -- legal

   -- Subtype range - two variables in one expression
   subtype S9 is Integer range 1 .. (B - A); -- illegal

   -- Derived type with range constraint
   type T1 is new Integer range A .. B; -- illegal

   --  Objects declared with anonymous subtypes, not initialized
   V1 : Integer range 1 .. 10;   -- legal
   V2 : Integer range N1 .. C10; -- legal
   V3 : Integer range 1 .. B;    -- illegal
   V4 : Integer range A .. 10;   -- illegal
   V5 : Integer range A .. B;    -- illegal
   V6 : Integer range 1 .. CB;   -- legal
   V7 : Integer range CA .. 10;  -- legal
   V8 : Integer range CA .. CB;  -- legal

   --  Objects declared with anonymous subtypes, initialized
   V9  : Integer range 1 .. 10 := B;   -- legal
   V10 : Integer range N1 .. C10 := B; -- legal
   V11 : Integer range 1 .. B := B;    -- illegal
   V12 : Integer range A .. 10 := B;   -- illegal
   V13 : Integer range A .. B := B;    -- illegal
   V14 : Integer range 1 .. CB := B;   -- legal
   V15 : Integer range CA .. 10 := B;  -- legal
   V16 : Integer range CA .. CB := B;  -- legal

   procedure Op1 (A : in out Integer)
     with Depends => (A => A);

   procedure Op2 (A : in     String;
                  L :    out Natural)
     with Depends => (L => A);

   procedure Op3 (A : in out String;
                  L :    out Natural)
     with Depends => ((L, A) => A);

   function Same_Length (S : String) return String;

end P;
