with Ada.Containers;
with Ada.Containers.Vectors;

generic
   type Element_Type is private;
   with function "=" (E1, E2 : Element_Type) return Boolean;
package Functional_Sequences with SPARK_Mode is
   type Sequence is private;

   function Get (S : Sequence; N : Natural) return Element_Type
   with Global => null;
   function Length (S : Sequence) return Natural
   with Global => null;
   function "=" (S1, S2 : Sequence) return Boolean is
     (Length (S1) = Length (S2)
      and then (for all N in Natural (0) .. Natural (Length (S1) - 1) =>
                  Get (S1, N) = Get (S2, N)))
   with Global => null;
   function Set (S : Sequence; N : Natural; E : Element_Type) return Sequence
     with Post =>
       (if N in 0 .. Length (S) - 1 then
          (Length (Set'Result) = Length (S)
           and then Get (Set'Result, N) = E
           and then (for all M in 0 .. Length (S) =>
               (if M /= N then Get (Set'Result, M) = Get (S, M)))));
   function Empty return Sequence with
     Post => Length (Empty'Result) = 0;
   function Sub (S : Sequence; N1, N2 : Natural) return Sequence with
     Post =>
       (if N1 in 0 .. Length (S) - 1 and then N2 in N1 .. Length (S) - 1 then
          (Length (Sub'Result) = N2 - N1 + 1
           and then (for all M in 0 .. N2 - N1 =>
                         Get (Sub'Result, M) = Get (S, M + N1))));
   function Find (S : Sequence; E : Element_Type) return Integer with
     Post => (if Find'Result >= 0 then Get (S, Find'Result) = E
              else (for all M in 0 .. Length (S) - 1 => Get (S, M) /= E));
   function Snoc (S : Sequence; E : Element_Type) return Sequence with
     Post => Length (Snoc'Result) = Length (S) + 1
     and then Get (Snoc'Result, Length (S)) = E
     and then (for all N in 0 .. Length (S) - 1 =>
                   Get (Snoc'Result, N) = Get (S, N));
private
   pragma SPARK_Mode (Off);

   package Element_Lists is new Ada.Containers.Vectors
     (Element_Type => Element_Type,
      Index_Type   => Natural,
      "="          => "=");
   use Element_Lists;

   type Sequence is new Vector with null record;
end Functional_Sequences;
