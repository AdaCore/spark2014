package Contradictions
with SPARK_Mode => On
is

   -- all of these tests are trying to prove that 1 = 0. For a non-specialist
   -- like me, it looks like the proof is fulfilled indeed, while in actuality,
   -- there is a contradiction somewhere in the prof that ends up creating a
   -- dead branch in the assertion. While correct from a pure proof point of
   -- view, it would be useful to report such dead branches (e.g. through
   -- the --proof-warning switch) as to give some fool-proof help.
   --
   -- The following tests are variations around the same idea, different ways
   -- to create the same kind of dead branches. It would be nice if any of these
   -- could generate a warning

   type X is null record
     with Predicate => (if False then 1 = 0);
   -- This is an obvious one, a False condition implies anything.

   type Y is new Positive
     with Predicate => (if Y < 0 then 1 = 0);
   -- A tad more subtle, but Y < 0 is impossible

   procedure P (V : out Integer)
     with Post => (if V > 0 then 1 = 0);
   -- In P, there's no path that leads to V > 0, so the branch is dead

   procedure P2 (V : in out Integer)
     with Pre => V in -10 .. 0,
     Post => (if V > 0 then 1 = 0);
   -- P should be able to lead to V > 0, but not under the precondition, which
   -- renders the path empty

   procedure P3 (V : out Integer)
     with Post => (if V <= 0 then True else 1 = 0);
   -- More of the same, the dead branch being on the else.

   type A is array (Integer range <>) of Integer;

   procedure P4 (V : out A)
     with Pre => V'Last < 1,
     Post => (for all I in 1 .. V'Last => V (I) = 0 and V (I) = 1);
   -- A variation of P2 where the post condition leads to an empty range

   procedure P5 (V : in out Integer)
     with Pre => V <= 0,
       Contract_Cases =>
       ((V in Integer'First .. 0) => True,
        others => V = 1 and V = 2);
   -- a variation using a contract case this time

   procedure P6 (V : in out Integer)
     with Pre => V <= 0,
       Post => (case V is when Integer'First .. 0 => True, when others => V = 1 and V = 2);
   -- a variation using a case expression this time

   procedure P7 (V : in out Integer)
     with Pre => V in -10 .. 0,
     Post => (V <= 0 or else 1 = 0);
   --  variation with "or else"

   procedure P8 (V : in out Integer)
     with Pre => V in -10 .. 0,
     Post => (V > 0 and then 1 = 0) or else (V <= 0);
   --  variation with "and then"

end Contradictions;
