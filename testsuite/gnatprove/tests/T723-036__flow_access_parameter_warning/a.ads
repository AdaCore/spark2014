package A with SPARK_Mode is
   type T is not null access Integer;

   --  type S is not null access constant Integer;
   --  Access constant types are intrinsically aliasing, thus illegal
   --  in SPARK!

   function F (X : T) return Boolean is
      (X.all = 3);
   --  Minimal reproducer from the ticket

   function H (X : access constant Integer) return Boolean is
      (X.all = 3);
   --  What SPARK suggests function F "should" look like

   procedure P (X      : in T;
                Result : out Boolean);
   --  P does not modify the contents of X.
   --  Note the signature doesn't guarantee this, so SPARK
   --  generates the same message as for function F.

   procedure Q (X      : in T;
                Result : out Boolean);
   --  Q modifies the contents of X

   procedure R (X      : access constant Integer;
                Result : out Boolean);
   --  Variation of P where the signature does guarantee
   --  the contents of X are not modified.
end A;
