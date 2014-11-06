package Foo
is
   type T1 is tagged record
      P : Boolean;
      Q : Boolean;
   end record;

   G : Boolean;

   procedure Test_01 (A : T1;
                      B : T1;
                      X : out Boolean;
                      Y : out Boolean)
   with Global  => (In_Out => G),
        Depends => (X => A,
                    Y => B,
                    G => G);

   procedure Test_02 (A : T1;
                      B : T1;
                      X : out Boolean;
                      Y : out Boolean)
   with Global => null;

   procedure Test_03 (A : T1;
                      B : T1;
                      X : out Boolean;
                      Y : out Boolean)
   with Global  => (In_Out => G),
        Depends => (X => A,
                    Y => (A, B, G),
                    G => G);

   procedure Test_04 (A : T1;
                      B : T1;
                      X : out Boolean;
                      Y : out Boolean)
   with Depends => (X => A,
                    Y => null,
                    null => B);

   procedure Test_05 (A : T1;
                      B : T1;
                      X : out Boolean;
                      Y : out Boolean)
   with Depends => (X => A,
                    Y => B);

   procedure Test_06 (A : T1;
                      B : T1;
                      X : out Boolean;
                      Y : out Boolean)
   with Depends => (X => A,
                    Y => B);

   function Test_07 (A, B : Boolean) return T1;

   function Test_08 (A, B : Boolean) return T1
     with Depends => (Test_08'Result => A,
                      null           => B);

   function Test_09 (A, B : Boolean) return T1
     with Depends => (Test_09'Result => A,
                      null           => B);

   function Test_10 (A, B : Boolean) return T1;

   type T2 is new T1 with null record;

   procedure Test_01 (A : T2;
                      B : T2;
                      X : out Boolean;
                      Y : out Boolean)
   with Global  => (Input => G),
        Depends => (X => (A, B),
                    Y => (B, G));

   procedure Test_02 (A : T2;
                      B : T2;
                      X : out Boolean;
                      Y : out Boolean)
   with Global  => null,
        Depends => (X => (A, B),
                    Y => B);

   procedure Test_03 (A : T2;
                      B : T2;
                      X : out Boolean;
                      Y : out Boolean)
   with Global => null;

   procedure Test_04 (A : T2;
                      B : T2;
                      X : out Boolean;
                      Y : out Boolean)
   with Depends => (X => A,
                    Y => B);

   procedure Test_05 (A : T2;
                      B : T2;
                      X : out Boolean;
                      Y : out Boolean)
   with Depends => (X => A,
                    Y => null,
                    null => B);

   procedure Test_06 (A : T2;
                      B : T2;
                      X : out Boolean;
                      Y : out Boolean)
   with Depends => (X => A,
                    Y => B,
                    null => G);

   function Test_07 (A, B : Boolean) return T2;

   function Test_08 (A, B : Boolean) return T2;

   function Test_09 (A, B : Boolean) return T2
     with Depends => (Test_09'Result => A,
                      null           => B);

   function Test_10 (A, B : Boolean) return T2
     with Depends => (Test_10'Result => A,
                      null           => B);

end Foo;
