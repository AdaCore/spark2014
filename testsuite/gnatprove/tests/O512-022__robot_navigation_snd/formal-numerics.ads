with Ada.Numerics;

package Formal.Numerics with
  SPARK_Mode
is
   pragma Pure;

   -- FIXME: external axiomatization of Pi and e as constants is not supported;
   -- instead, we define them as inlined functions.

     Pi : constant := Ada.Numerics.Pi;
--     e : constant := Ada.Numerics.e;

   --function Pi return Float is (Ada.Numerics.Pi);
   --pragma inline(Pi);

   function e return Float is (Ada.Numerics.e);
   pragma Inline(e);

   -- FIXME: rewrite bounds as static invariants (which are not yet supported by GNATprove).

   -- Formal representation of (0.0 ; +Inf) interval.
   subtype Positive_Float is Float range 0.0 .. Float'Last;

   -- Formal representation of <0.0 ; +Inf) interval.
   subtype NonNegative_Float is Float range 0.0 .. Float'Last;

   -- Formal representation of (-Inf ; 0.0) interval.
   subtype Negative_Float is Float range Float'First .. 0.0;

   -- Formal representation of (-Inf ; +Inf) interval.
   subtype Unbounded_Float is Standard.Float;

   -- Formal representation of (-Inf ; 0) U (0 ; +Inf) interval.
   subtype NonZero_Float is Standard.Float;
end;
