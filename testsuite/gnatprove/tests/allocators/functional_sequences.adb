pragma Ada_2012;
package body Functional_Sequences with SPARK_Mode => Off is
   function Get (S : Sequence; N : Positive) return Element_Type is
     (Element (S, N));
   function Length (S : Sequence) return Natural is
     (Natural (Length (Vector (S))));

   function "=" (S1, S2 : Sequence) return Boolean is
     (Length (S1) = Length (S2)
      and then (for all N in 1 .. Natural (Length (Vector (S1))) =>
                   Get (S1, N) = Get (S2, N)));

   function Is_Replace
     (S : Sequence; N : Positive; E : Element_Type; Result : Sequence)
      return Boolean is
     (N in 1 .. Length (S)
      and then Length (Result) = Length (S)
      and then Get (Result, N) = E
      and then (for all M in 1 .. Natural (Length (Vector (S))) =>
                  (if M /= N then Get (Result, M) = Get (S, M))));

   function Replace (S : Sequence; N : Positive; E : Element_Type)
                     return Sequence
   is
      SS : Sequence := Copy (S);
   begin
      Replace_Element (SS, N, E);
      return SS;
   end Replace;

   function Is_Prepend
     (S : Sequence; E : Element_Type; Result : Sequence) return Boolean is
     (Length (Result) = Length (S) + 1
      and then Get (Result, 1) = E
      and then (for all M in 1 .. Natural (Length (Vector (S))) =>
                   Get (Result, M + 1) = Get (S, M)));

   function Prepend (S : Sequence; E : Element_Type) return Sequence
   is
      SS : Sequence := Copy (S);
   begin
      Prepend (SS, E);
      return SS;
   end Prepend;

   function Is_Add
     (S : Sequence; E : Element_Type; Result : Sequence) return Boolean is
     (Length (Result) = Length (S) + 1
      and then Get (Result, Length (Result)) = E
      and then (for all M in 1 .. Natural (Length (Vector (S))) =>
                   Get (Result, M) = Get (S, M)));

   function Add (S : Sequence; E : Element_Type) return Sequence
   is
      SS : Sequence := Copy (S);
   begin
      Append (SS, E);
      return SS;
   end Add;

   function Is_Removed_At
     (S : Sequence; N : Positive; Result : Sequence) return Boolean
   is
     (Length (Result) = Length (S) - 1
      and then (for all M in 1 .. Natural'(Length (S)) =>
                  (if M < N then Get (Result, M) = Get (S, M)
                   elsif M > N then Get (Result, M - 1) = Get (S, M))));

   function Remove_At (S : Sequence; N : Positive) return Sequence is
      SS : Sequence := Copy (S);
   begin
      Delete (SS, N);
      return SS;
   end Remove_At;

end Functional_Sequences;
