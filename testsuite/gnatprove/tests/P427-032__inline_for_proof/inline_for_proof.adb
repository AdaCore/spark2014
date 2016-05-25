package body Inline_For_Proof with SPARK_Mode is

   function Get (X : A; I : Positive) return T is
     (if B then X (I) else Y (I));

   procedure P (X : A) is null;

   function Get2 (X : A; I : Positive) return T is
     (if B then X (I) else Y (I));

   procedure P2 (X : A) is null;

end Inline_For_Proof;
