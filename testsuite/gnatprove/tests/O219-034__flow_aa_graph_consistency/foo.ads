package Foo
is

   procedure Test_01 (A, B : Integer;
                      C    : out Integer)
   with Global  => null,
        Depends => (C => (A, B)),
        Post    => C = A or C = B;

   procedure Test_02 (A, B : Integer;
                      C    : out Integer)
   with Global  => null,
        Depends => (C    => A,
                    null => B),
        Post    => C = A;

   procedure Test_03 (A, B : Integer;
                      C    : out Integer)
   with Global => null,
        Depends => (C    => B,
                    null => A),
        Post    => C = B;

end Foo;
