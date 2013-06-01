package T is
   type S is range 1 .. 10_000_000;
   type A is array (S range <>) of S;
   type R (I : S) is record
      C : A (1 .. I);
   end record;
end T;
