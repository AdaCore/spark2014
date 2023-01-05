procedure Test_Predicates_2 (C : Integer) with SPARK_Mode is

   --  Test with procedures modifying the content of a type with predicate

   type T1 is record
      F : Integer;
      G : Integer;
   end record;

   type T2 is record
      H : T1;
   end record with
     Predicate => H.F < H.G;

   procedure P (X : T1) with
     Global => null,
     Annotate => (GNATprove, Always_Return),
     Import,
     Relaxed_Initialization => X;

   procedure R (X : out T1) with
     Global => null,
     Annotate => (GNATprove, Always_Return),
     Import,
     Post => X.F < X.G;

   procedure Q (X : in out T1) with
     Global => null,
     Annotate => (GNATprove, Always_Return),
     Import,
     Relaxed_Initialization => X,
     Post => X'Initialized and then X.F < X.G;

   procedure S (X : in out T1) with
     Global => null,
     Annotate => (GNATprove, Always_Return),
     Import,
     Relaxed_Initialization => X;

   X : T2 with Relaxed_Initialization;

begin
   --  No predicate checks for OUT parameters

   if C = 0 then
      R (X.H);  --@PREDICATE_CHECK:PASS @INIT_BY_PROOF:PASS

   --  X.H is read, the predicate is checked even if the parameter call does
   --  not mandate it.
   elsif C = 1 then
      P (X.H);  --@INIT_BY_PROOF:FAIL @PREDICATE_CHECK:FAIL

   --  The predicate check on output is proved thanks to the post of Q
   elsif C = 2 then
      X := (H => (1, 2));
      Q (X.H);  --@INIT_BY_PROOF:PASS

   --  The predicate check on output fails
   elsif C = 3 then
      X := (H => (1, 2));
      S (X.H);  --@INIT_BY_PROOF:FAIL @PREDICATE_CHECK:FAIL
   end if;
end Test_Predicates_2;
