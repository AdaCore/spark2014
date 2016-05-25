pragma Ada_2012;
package body Functional_Sequences with SPARK_Mode => Off is
   function Get (S : Sequence; N : Extended_Index) return Element_Type is
     (Element_Lists.Vectors.Element (S, N));

   function Length (S : Sequence) return Count_Type is
     (Element_Lists.Vectors.Length (S));

   function "=" (S1, S2 : Sequence) return Boolean is
     (Element_Lists.Vectors.Length (S1) = Element_Lists.Vectors.Length (S2)
      and then
        (for all N in Index_Type'First ..
             (Index_Type'Val
                  ((Index_Type'Pos (Index_Type'First) - 1) +
                     Element_Lists.Vectors.Length (S1))) =>
                Get (S1, N) = Get (S2, N)));

   function Is_Replace
     (S : Sequence; N : Index_Type; E : Element_Type; Result : Sequence)
      return Boolean is
     (N in Index_Type'First ..
             (Index_Type'Val
                  ((Index_Type'Pos (Index_Type'First) - 1) +
                     Element_Lists.Vectors.Length (S)))
      and then Element_Lists.Vectors.Length (Result) =
        Element_Lists.Vectors.Length (S)
      and then Get (Result, N) = E
      and then
        (for all M in  Index_Type'First ..
             (Index_Type'Val
                  ((Index_Type'Pos (Index_Type'First) - 1) +
                     Element_Lists.Vectors.Length (S))) =>
             (if M /= N then Get (Result, M) = Get (S, M))));

   function Replace (S : Sequence; N : Index_Type; E : Element_Type)
                     return Sequence
   is
   begin
      return SS : Sequence do
         Element_Lists.Vectors.Assign (SS, S);
         Element_Lists.Vectors.Replace_Element (SS, N, E);
      end return;
   end Replace;

   function Is_Prepend
     (S : Sequence; E : Element_Type; Result : Sequence) return Boolean is
     (Element_Lists.Vectors.Length (Result) =
        Element_Lists.Vectors.Length (S) + 1
      and then Get (Result, Index_Type'First) = E
      and then
        (for all M in Index_Type'Succ (Index_Type'First) ..
             (Index_Type'Val
                  ((Index_Type'Pos (Index_Type'First) - 1) +
                     Element_Lists.Vectors.Length (Result))) =>
              Get (Result, M) = Get (S, M)));

   function Prepend (S : Sequence; E : Element_Type) return Sequence is
   begin
      return SS : Sequence do
         Element_Lists.Vectors.Assign (SS, S);
         Element_Lists.Vectors.Prepend (SS, E);
      end return;
   end Prepend;

   function Is_Add
     (S : Sequence; E : Element_Type; Result : Sequence) return Boolean is
     (Element_Lists.Vectors.Length (Result) =
        Element_Lists.Vectors.Length (S) + 1
      and then Get (Result, Index_Type'Val
                    ((Index_Type'Pos (Index_Type'First) - 1) +
                       Element_Lists.Vectors.Length (Result))) = E
      and then
        (for all M in Index_Type'First ..
             (Index_Type'Val
                  ((Index_Type'Pos (Index_Type'First) - 1) +
                     Element_Lists.Vectors.Length (S))) =>
              Get (Result, M) = Get (S, M)));

   function Add (S : Sequence; E : Element_Type) return Sequence is
   begin
      return SS : Sequence do
         Element_Lists.Vectors.Assign (SS, S);
         Element_Lists.Vectors.Append (SS, E);
      end return;
   end Add;

   function Is_Deleted
     (S : Sequence; N : Index_Type; Result : Sequence) return Boolean
   is
     (Length (Result) = Length (S) - 1
      and then (for all M in Index_Type'First .. Index_Type'Val
                  ((Index_Type'Pos (Index_Type'First) - 1) + Length (Result)) =>
                  (if Index_Type'Pos(M) < Index_Type'Pos(N) then Get (Result, M) = Get (S, M)
                   elsif Index_Type'Pos(M) >= Index_Type'Pos(N) then Get (Result, M) = Get (S, Index_Type'Succ(M)))));

   function Delete (S : Sequence; N : Index_Type) return Sequence is
   begin
      return SS : Sequence do
         Element_Lists.Vectors.Assign (SS, S);
         Element_Lists.Vectors.Delete (SS, N);
      end return;
   end Delete;

   function Iter_First (S : Sequence) return Extended_Index
   is (Index_Type'First);
   function Iter_Next (S : Sequence; I : Extended_Index) return Extended_Index
   is
     (if I = Extended_Index'Last then Extended_Index'First
      else Extended_Index'Succ (I));
   function Iter_Has_Element (S : Sequence; I : Extended_Index) return Boolean
   is
     (I in Index_Type'First ..
        (Index_Type'Val
             ((Index_Type'Pos (Index_Type'First) - 1) +
                  Element_Lists.Vectors.Length (S))));
end Functional_Sequences;
