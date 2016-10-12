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
package body Conts.Functional.Sequences with SPARK_Mode => Off is
   use Containers;

   pragma Assertion_Policy
      (Pre => Suppressible, Ghost => Suppressible, Post => Ignore);

   ---------
   -- "=" --
   ---------

   function "=" (S1, S2 : Sequence) return Boolean is
     (S1.Content = S2.Content);

   ---------
   -- Add --
   ---------

   function Add (S : Sequence; E : Element_Type) return Sequence is
     (Content => Add (S.Content, E));

   ---------
   -- Get --
   ---------

   function Get (S : Sequence; N : Extended_Index) return Element_Type is
     (Get (S.Content, N));

   ------------
   -- Is_Add --
   ------------

   function Is_Add
     (S : Sequence; E : Element_Type; Result : Sequence) return Boolean is
     (Length (Result) = Length (S) + 1
      and then Get (Result, Index_Type'Val
                    ((Index_Type'Pos (Index_Type'First) - 1) +
                       Length (Result))) = E
      and then
        (for all M in Index_Type'First ..
             (Index_Type'Val
                  ((Index_Type'Pos (Index_Type'First) - 1) + Length (S))) =>
              Get (Result, M) = Get (S, M)));

   ------------
   -- Is_Set --
   ------------

   function Is_Set
     (S : Sequence; N : Index_Type; E : Element_Type; Result : Sequence)
      return Boolean is
     (N in Index_Type'First ..
             (Index_Type'Val
                  ((Index_Type'Pos (Index_Type'First) - 1) + Length (S)))
      and then Length (Result) = Length (S)
      and then Get (Result, N) = E
      and then
        (for all M in  Index_Type'First ..
             (Index_Type'Val
                  ((Index_Type'Pos (Index_Type'First) - 1) + Length (S))) =>
             (if M /= N then Get (Result, M) = Get (S, M))));

   ----------
   -- Last --
   ----------

   function Last (S : Sequence) return Extended_Index is
     (Index_Type'Val ((Index_Type'Pos (Index_Type'First) - 1) + Length (S)));

   ------------
   -- Length --
   ------------

   function Length (S : Sequence) return Count_Type is
     (Length (S.Content));

   ---------
   -- Set --
   ---------

   function Set (S : Sequence; N : Index_Type; E : Element_Type)
                 return Sequence is
     (Content => Set (S.Content, N, E));
end Conts.Functional.Sequences;
