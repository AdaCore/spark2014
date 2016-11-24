------------------------------------------------------------------------------
--                     Copyright (C) 2016, AdaCore                          --
--                                                                          --
-- This library is free software;  you can redistribute it and/or modify it --
-- under terms of the  GNU General Public License  as published by the Free --
-- Software  Foundation;  either version 3,  or (at your  option) any later --
-- version. This library is distributed in the hope that it will be useful, --
-- but WITHOUT ANY WARRANTY;  without even the implied warranty of MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE.                            --
--                                                                          --
-- As a special exception under Section 7 of GPL version 3, you are granted --
-- additional permissions described in the GCC Runtime Library Exception,   --
-- version 3.1, as published by the Free Software Foundation.               --
--                                                                          --
-- You should have received a copy of the GNU General Public License and    --
-- a copy of the GCC Runtime Library Exception along with this program;     --
-- see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see    --
-- <http://www.gnu.org/licenses/>.                                          --
--                                                                          --
------------------------------------------------------------------------------

pragma Ada_2012;
with Conts;           use Conts;
private with Conts.Functional.Base;

generic
   type Index_Type is (<>);
   --  To avoid Constraint_Error being raised at runtime, Index_Type'Base
   --  should have at least one more element at the left than Index_Type.

   type Element_Type (<>) is private;
package Conts.Functional.Sequences with SPARK_Mode is
   pragma Annotate (GNATprove, Terminating, Sequences);
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

   function Last (S : Sequence) return Extended_Index with
     Global => null,
     Post => Last'Result =
       Index_Type'Val ((Index_Type'Pos (Index_Type'First) - 1) + Length (S));

   function First return Extended_Index is (Index_Type'First);

   function Get (S : Sequence; N : Extended_Index) return Element_Type
   --  Get ranges over Extended_Index so that it can be used for iteration.

   with
     Global => null,
     Pre    => N in Index_Type'First .. Last (S);

   function "=" (S1, S2 : Sequence) return Boolean with
   --  Extensional equality over sequences.

     Global => null,
     Post   => "="'Result =
       (Length (S1) = Length (S2)
        and then (for all N in Index_Type'First .. Last (S1) =>
            Get (S1, N) = Get (S2, N)));

   function Is_Set
     (S : Sequence; N : Index_Type; E : Element_Type; Result : Sequence)
      return Boolean
   --  Returns True if Result is S where the Nth element has been replaced by
   --  E.

   with
     Global => null,
       Post   => Is_Set'Result =
         (N in Index_Type'First .. Last (S)
          and then Length (Result) = Length (S)
          and then Get (Result, N) = E
          and then (for all M in Index_Type'First .. Last (S) =>
              (if M /= N then Get (Result, M) = Get (S, M))));

   function Set
     (S : Sequence; N : Index_Type; E : Element_Type) return Sequence
   --  Returns S where the Nth element has been replaced by E.
   --  Is_Set (S, N, E, Result) should be instead of than
   --  Result = Set (S, N, E) whenever possible both for execution and for
   --  proof.

   with
     Global => null,
     Pre    => N in Index_Type'First .. Last (S),
     Post   => Is_Set (S, N, E, Set'Result);

   function Is_Add
     (S : Sequence; E : Element_Type; Result : Sequence) return Boolean
   --  Returns True if Result is S appended with E.

   with
     Global => null,
     Post   => Is_Add'Result =
         (Length (Result) = Length (S) + 1
          and then Get (Result, Last (Result)) = E
          and then (for all M in Index_Type'First .. Last (S) =>
              Get (Result, M) = Get (S, M)));

   function Add (S : Sequence; E : Element_Type) return Sequence with
   --  Returns S appended with E.
   --  Is_Add (S, E, Result) should be used instead of Result = Add (S, E)
   --  whenever possible both for execution and for proof.

     Global => null,
     Pre    => Length (S) < Count_Type'Last and Last (S) < Index_Type'Last,
     Post   => Is_Add (S, E, Add'Result);

   ---------------------------
   --  Iteration Primitives --
   ---------------------------

   function Iter_First (S : Sequence) return Extended_Index;
   function Iter_Has_Element (S : Sequence; I : Extended_Index) return Boolean
   with
     Post => Iter_Has_Element'Result = (I in Index_Type'First .. Last (S));
   pragma Annotate (GNATprove, Inline_For_Proof, Iter_Has_Element);

   function Iter_Next (S : Sequence; I : Extended_Index) return Extended_Index
     with
       Pre => Iter_Has_Element (S, I);

private
   pragma SPARK_Mode (Off);

   package Containers is new Conts.Functional.Base
     (Index_Type   => Index_Type,
      Element_Type => Element_Type);

   type Sequence is record
      Content : Containers.Container;
   end record;

   function Iter_First (S :
                        Sequence) return Extended_Index
   is (Index_Type'First);
   function Iter_Next (S : Sequence; I : Extended_Index) return Extended_Index
   is
     (if I = Extended_Index'Last then Extended_Index'First
      else Extended_Index'Succ (I));

   function Iter_Has_Element (S : Sequence; I : Extended_Index) return Boolean
   is
     (I in Index_Type'First ..
        (Index_Type'Val
             ((Index_Type'Pos (Index_Type'First) - 1) + Length (S))));
end Conts.Functional.Sequences;
