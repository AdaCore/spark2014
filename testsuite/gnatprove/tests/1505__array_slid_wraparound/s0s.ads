package S0s
  with SPARK_Mode
is

   type I is mod 2 ** 64;
   type U is array (I range <>) of Integer;
   subtype Two is U (0 .. 1);

   function Eq (X, Y : U) return Boolean
   is (X'First = Y'First and then X'Last = Y'Last and then X = Y)
   with Ghost, Annotate => (GNATprove, Logical_Equal);

   function Small (J : I) return Boolean
   is (J < I'Last)
   with Ghost;

   procedure Lemma_False (A, B : Two; K : I)
   with
     Ghost,
     Global => null,
     Pre    => A (0) /= B (0) and K = I'Last,
     Post   => False; --  @POSTCONDITION:FAIL

   type U2 is array (I range <>, I range <>) of Integer;
   subtype Two2 is U2 (0 .. 1, 0 .. 1);

   function Eq (X, Y : U2) return Boolean
   is (X'First (1) = Y'First (1)
       and then X'Last (1) = Y'Last (1)
       and then X'First (2) = Y'First (2)
       and then X'Last (2) = Y'Last (2)
       and then X = Y)
   with Ghost, Annotate => (GNATprove, Logical_Equal);

   procedure Lemma_False_2_2 (A, B : Two2; K : I)
   with
     Ghost,
     Global => null,
     Pre    => A (0, 0) /= B (0, 0) and K = I'Last,
     Post   => False; --  @POSTCONDITION:FAIL

   type U3 is array (I range <>, I range <>, I range <>) of Integer;
   subtype Two3 is U3 (0 .. 1, 0 .. 1, 0 .. 1);

   function Eq (X, Y : U3) return Boolean
   is (X'First (1) = Y'First (1)
       and then X'Last (1) = Y'Last (1)
       and then X'First (2) = Y'First (2)
       and then X'Last (2) = Y'Last (2)
       and then X'First (3) = Y'First (3)
       and then X'Last (3) = Y'Last (3)
       and then X = Y)
   with Ghost, Annotate => (GNATprove, Logical_Equal);

   procedure Lemma_False_3_3 (A, B : Two3; K : I)
   with
     Ghost,
     Global => null,
     Pre    => A (0, 0, 0) /= B (0, 0, 0) and K = I'Last,
     Post   => False; --  @POSTCONDITION:FAIL

   type U4 is
     array (I range <>, I range <>, I range <>, I range <>) of Integer;
   subtype Two4 is U4 (0 .. 1, 0 .. 1, 0 .. 1, 0 .. 1);

   function Eq (X, Y : U4) return Boolean
   is (X'First (1) = Y'First (1)
       and then X'Last (1) = Y'Last (1)
       and then X'First (2) = Y'First (2)
       and then X'Last (2) = Y'Last (2)
       and then X'First (3) = Y'First (3)
       and then X'Last (3) = Y'Last (3)
       and then X'First (4) = Y'First (4)
       and then X'Last (4) = Y'Last (4)
       and then X = Y)
   with Ghost, Annotate => (GNATprove, Logical_Equal);

   procedure Lemma_False_4_4 (A, B : Two4; K : I)
   with
     Ghost,
     Global => null,
     Pre    => A (0, 0, 0, 0) /= B (0, 0, 0, 0) and K = I'Last,
     Post   => False; --  @POSTCONDITION:FAIL

end S0s;
