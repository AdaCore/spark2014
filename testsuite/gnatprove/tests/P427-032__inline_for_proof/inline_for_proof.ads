package Inline_For_Proof with SPARK_Mode is

   subtype T is Natural range 0 .. 10;
   type A is array (1 .. 100) of T;

   Y : A;
   B : Boolean;

   function Get (X : A; I : Positive) return T with
     Pre  => I in X'Range,
     Post => Get'Result = (if B then X (I) else Y (I));

   pragma Annotate (GNATprove, Inline_For_Proof, Entity => Get);

   procedure P (X : A) with
     Pre  => (for all E of X => (for some F of Y => E = F)),
     Post => (for all I in X'Range =>
                (for some J in Y'Range => Get (X, I) = Get (Y, J)));

   function Get2 (X : A; I : Positive) return T with
     Pre  => I in X'Range,
     Post => Get2'Result = (if B then X (I) else Y (I));

   procedure P2 (X : A) with
     Pre  => (for all E of X => (for some F of Y => E = F)),
     Post => (for all I in X'Range =>
                (for some J in Y'Range => Get2 (X, I) = Get2 (Y, J)));

end Inline_For_Proof;
