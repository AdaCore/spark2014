pragma Ada_2012;
with Conts;           use Conts;
with Conts.Vectors.Indefinite_Unbounded;

generic
   type Index_Type is (<>);
   --  To avoid Constraint_Error being raised at runtime, Index_Type'Base
   --  should have at least one more element at the left than Index_Type.

   type Element_Type (<>) is private;
package Functional_Sequences with SPARK_Mode is

   subtype Extended_Index is Index_Type'Base range
     Index_Type'Pred (Index_Type'First) .. Index_Type'Last;
   --  Index_Type with one more element to the left.
   --  This type is never used but it forces GNATprove to check that there is
   --  room for one more element at the left of Index_Type.

   type Sequence is private
     with Default_Initial_Condition => Length (Sequence) = 0,
     Iterable => (First       => Iter_First,
                  Has_Element => Iter_Has_Element,
                  Next        => Iter_Next,
                  Element     => Get);
   --  Sequences are empty when default initialized.
   --  Quantification over sequences can be done using the regular
   --  quantification over its range or directky on its elements using for of.

   --  Sequences are axiomatized using Length and Get providing respectively
   --  the length of a sequence and an accessor to its Nth element:

   function Length (S : Sequence) return Count_Type with
     Global => null,
     Post => (Index_Type'Pos (Index_Type'First) - 1) + Length'Result <=
       Index_Type'Pos (Index_Type'Last);

   function Get (S : Sequence; N : Extended_Index) return Element_Type
   --  Get ranges over Extended_Index so that it can be used for iteration.

   with
     Global => null,
     Pre    => N in Index_Type'First ..
          (Index_Type'Val
             ((Index_Type'Pos (Index_Type'First) - 1) + Length (S)));

   function "=" (S1, S2 : Sequence) return Boolean with
   --  Extensional equality over sequences.

     Global => null,
     Post   => "="'Result =
       (Length (S1) = Length (S2)
        and then (for all N in Index_Type'First ..
          (Index_Type'Val
             ((Index_Type'Pos (Index_Type'First) - 1) + Length (S1))) =>
            Get (S1, N) = Get (S2, N)));

   function Is_Replace
     (S : Sequence; N : Index_Type; E : Element_Type; Result : Sequence)
      return Boolean
   --  Returns True if Result is S where the Nth element has been replaced by
   --  E.

   with
     Global => null,
       Post   => Is_Replace'Result =
         (N in Index_Type'First ..
          (Index_Type'Val
             ((Index_Type'Pos (Index_Type'First) - 1) + Length (S)))
          and then Length (Result) = Length (S)
          and then Get (Result, N) = E
          and then (for all M in Index_Type'First ..
            (Index_Type'Val
               ((Index_Type'Pos (Index_Type'First) - 1) + Length (S))) =>
              (if M /= N then Get (Result, M) = Get (S, M))));

   function Replace
     (S : Sequence; N : Index_Type; E : Element_Type) return Sequence
   --  Returns S where the Nth element has been replaced by E.
   --  Is_Replace (S, N, E, Result) should be instead of than
   --  Result = Replace (S, N, E) whenever possible both for execution and for
   --  proof.

   with
     Global => null,
     Pre    => N in Index_Type'First ..
          (Index_Type'Val
             ((Index_Type'Pos (Index_Type'First) - 1) + Length (S))),
     Post   => Is_Replace (S, N, E, Replace'Result);

   function Is_Add
     (S : Sequence; E : Element_Type; Result : Sequence) return Boolean
   --  Returns True if Result is S appended with E.

   with
     Global => null,
     Post   => Is_Add'Result =
         (Length (Result) = Length (S) + 1
          and then Get (Result, Index_Type'Val
            ((Index_Type'Pos (Index_Type'First) - 1) + Length (Result))) = E
          and then (for all M in Index_Type'First ..
            (Index_Type'Val
               ((Index_Type'Pos (Index_Type'First) - 1) + Length (S))) =>
              Get (Result, M) = Get (S, M)));

   function Add (S : Sequence; E : Element_Type) return Sequence with
   --  Returns S appended with E.
   --  Is_Add (S, E, Result) should be used instead of Result = Add (S, E)
   --  whenever possible both for execution and for proof.

     Global => null,
     Pre    => Length (S) < Count_Type'Last
     and then ((Index_Type'Pos (Index_Type'First) - 1) + Length (S)) <
       Index_Type'Pos (Index_Type'Last),
     Post   => Is_Add (S, E, Add'Result);

   function Is_Prepend
     (S : Sequence; E : Element_Type; Result : Sequence) return Boolean
   --  Returns True if Result is S prepended with E.

   with
     Global => null,
     Post   => Is_Prepend'Result =
         (Length (Result) = Length (S) + 1
          and then Get (Result, Index_Type'First) = E
          and then (for all M in Index_Type'Succ (Index_Type'First) ..
                      Index_Type'Val
                      ((Index_Type'Pos (Index_Type'First) - 1) + Length (Result))
            => Get (Result, M) = Get (S, Index_Type'Pred (M)))
          and then (for all M in Index_Type'First ..
                      Index_Type'Val
                      ((Index_Type'Pos (Index_Type'First) - 1) + Length (S)) =>
              Get (Result, Index_Type'Succ (M)) = Get (S, M)));

   function Prepend (S : Sequence; E : Element_Type) return Sequence with
   --  Returns S prepended with E.
   --  Is_Prepend (S, E, Result) should be used instead of Result = Prepend (S, E)
   --  whenever possible both for execution and for proof.

     Global => null,
     Post   => Is_Prepend (S, E, Prepend'Result);

   function Is_Deleted
     (S : Sequence; N : Index_Type; Result : Sequence) return Boolean
   with
     Global => null,
     Pre    => N in Index_Type'First .. Index_Type'Last,
     Post   => Is_Deleted'Result =
     (Length (Result) = Length (S) - 1
      and then (for all M in Index_Type'First .. Index_Type'Val
                  ((Index_Type'Pos (Index_Type'First) - 1) + Length (Result)) =>
                  (if Index_Type'Pos(M) < Index_Type'Pos(N) then Get (Result, M) = Get (S, M)
                   elsif Index_Type'Pos(M) >= Index_Type'Pos(N) then Get (Result, M) = Get (S, Index_Type'Succ(M)))));

   function Delete (S : Sequence; N : Index_Type) return Sequence
   with
     Global => null,
     Pre    => N in Index_Type'First .. Index_Type'Last,
     Post   => Is_Deleted (S, N, Delete'Result);

   function Iter_First (S : Sequence) return Extended_Index;
   function Iter_Has_Element (S : Sequence; I : Extended_Index) return Boolean
   with
     Post => Iter_Has_Element'Result =
         (I in Index_Type'First ..
            (Index_Type'Val
               ((Index_Type'Pos (Index_Type'First) - 1) + Length (S))));
   pragma Annotate (GNATprove, Inline_For_Proof, Iter_Has_Element);

   function Iter_Next (S : Sequence; I : Extended_Index) return Extended_Index
     with
       Pre => Iter_Has_Element (S, I);

private
   pragma SPARK_Mode (Off);

   type Neither_Controlled_Nor_Limited is tagged null record;

   --  Functional sequences are neither controlled nor limited. As a result,
   --  no primitive should be provided to modify them. Note that we
   --  should definitely not use limited types for those as we need to apply
   --  'Old on them.
   --  ??? Should we make them controlled to avoid memory leak ?

   package Element_Lists is new Conts.Vectors.Indefinite_Unbounded
     (Element_Type        => Element_Type,
      Index_Type          => Index_Type,
      Container_Base_Type => Neither_Controlled_Nor_Limited);

   type Sequence is new Element_Lists.Vector with null record;
end Functional_Sequences;
