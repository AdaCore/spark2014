package A with SPARK_Mode is
   type T is not null access Integer;
   type T_Priv is private;

   type Foo is record
      A : Integer;
   end record;
   type S is not null access Foo;

   --  SPARK's old warning was that T should look like the following:

   --  type T is not null access constant Integer;

   --  However access constant types are intrinsically aliasing, thus
   --  illegal in SPARK!

   function F (X : T) return Boolean is
      (X.all = 3);
   --  Minimal reproducer from the ticket
   --  Following fixes in the code, SPARK no longer emits a warning because
   --  Flow is aware that parameter X is immutable.

   function D (X : S) return Boolean is
      (X.all.A = 3);
   --  As F but using a more complex type

   function H (X : access constant Integer) return Boolean is
      (X.all = 3);
   --  Regression check; this mimics the form recommended by the new
   --  warning emitted against procedures

   function I (X : access constant Foo) return Boolean is
      (X.all.A = 3);
   --  Regression check.

   procedure P (X      : in T;  --  Warn about this
                Result : out Boolean);
   --  P does not modify the contents of X, however the
   --  above signature doesn't guarantee this. SPARK should
   --  generate a warning message.

   procedure Q (X      : in T;
                Result : out Boolean);
   --  Q modifies the contents of X but not where X points; this is
   --  the "correct" form of signature for this case so SPARK should
   --  not generate a warning.

   procedure R (X      : access constant Integer;
                Result : out Boolean);
   --  Variation of P where the signature does guarantee
   --  the contents of X are not modified.

   procedure R_Record (X      : access constant Foo;
                       Result : out Boolean);
   --  Variation of R with more complex type.

   procedure P_Priv (Z      : in T_Priv;
                     Result : out Boolean);

   --  Regression check: P1_Priv doesn't modify Z
   procedure P1_Priv (Z      : in out T_Priv;  --  Should warn
                      Result : out Boolean);
private
   --  Straightforwardly private version of T.
   type T_Priv is not null access Integer;
end A;
