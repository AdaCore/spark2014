procedure Test_Predicates
  with
    SPARK_Mode => On
is

   function Rand (I : Integer) return Boolean with
     Global => null,
     Annotate => (GNATprove, Always_Return),
     Import;

   type Holder is record
      C : Integer;
   end record;

   type R1 is record
      F, G : Holder;
   end record with Predicate => F.C < G.C;

   --  Test that initialization is required for parameters of type R1 as it has
   --  a predicate which requires initialization.

   --  R1 has a predicate, it shall be initialized on input
   procedure P (X : in out R1) with
     Relaxed_Initialization => X
   is
   begin
      pragma Assert (X.F.C < X.G.C);  --@INIT_BY_PROOF:NONE
      X := ((C => 2), (C => 3));
   end P;

   --  R1 has a predicate, it shall be initialized on output
   procedure Q (X : out R1) with --@INIT_BY_PROOF:FAIL
     Relaxed_Initialization => X
   is
   begin
      if Rand (0) then
      X := ((C => 2), (C => 3));
      end if;
   end Q;

   --  R1 has a predicate, it shall be initialized on output
   function Default return R1 with
     Relaxed_Initialization => Default'Result
   is
      X : R1 with Relaxed_Initialization;
   begin
      return X; --@INIT_BY_PROOF:FAIL --@PREDICATE_CHECK:FAIL
   end Default;

   --  Same checks using a derived type of R1 with Relaxed_Initialization

   type S1 is new R1 with Relaxed_Initialization;

   --  R1 has a predicate, it shall be initialized on input
   procedure P (X : in out S1) is
   begin
      pragma Assert (X.F.C < X.G.C);  --@INIT_BY_PROOF:NONE
      X := ((C => 2), (C => 3));
   end P;

   --  R1 has a predicate, it shall be initialized on output
   procedure Q (X : out S1) is --@INIT_BY_PROOF:FAIL
   begin
      if Rand (0) then
         X := ((C => 2), (C => 3));
      end if;
   end Q;

   --  R1 has a predicate, it shall be initialized on output
   function Default return S1 is
      X : S1 with Relaxed_Initialization;
   begin
      return X; --@INIT_BY_PROOF:FAIL --@PREDICATE_CHECK:FAIL
   end Default;

   --  The predicates and initialization are not enforced on subcomponents

   type R2 is record
      H, I : R1;
   end record;

   --  R2 does not have a predicate, it might not be initialized on input
   procedure P (X : in out R2) with
     Relaxed_Initialization => X,
     Pre  => X.H'Initialized,
     Post => X'Initialized
   is
   begin
      pragma Assert (X.H.F.C < X.H.G.C); --@INIT_BY_PROOF:PASS
      if Rand (0) then
         pragma Assert (X.I.F.C < X.I.G.C); --@INIT_BY_PROOF:FAIL
      end if;
      X.I := ((C => 2), (C => 3));
   end P;

   --  The predicate of X.H might not hold on input even if its components are
   --  initialized. Such an object cannot be constructed from SPARK code though.
   procedure P_Strange (X : in out R2) with
     Relaxed_Initialization => X,
     Pre => X.H.F'Initialized and X.H.G'Initialized
   is
   begin
      pragma Assert (X.H.F.C < X.H.G.C); -- @ASSERT:FAIL
      X.I := ((C => 2), (C => 3));
   end P_Strange;

   --  R2 does not have a predicate, it might not be initialized on output
   procedure Q (X : out R2) with --@INIT_BY_PROOF:NONE
     Relaxed_Initialization => X
   is
   begin
      if Rand (0) then
         X := (((C =>0), (C =>1)), ((C =>2), (C =>3)));
      end if;
   end Q;

   --  R2 does not have a predicate, it might not be initialized on output
   function Default return R2 with
     Relaxed_Initialization => Default'Result
   is
      X : R2 with Relaxed_Initialization;
   begin
      return X; --@INIT_BY_PROOF:NONE
   end Default;

   --  R2 does not have a predicate, it might not be initialized on output but
   --  R1 has a predicate, so shall be initialized on output.
   function Get (X : R2) return R1 with
     Pre => X.I'Initialized,
     Relaxed_Initialization => (Get'Result, X)
   is
   begin
      if Rand (0) then
         return X.H; --@INIT_BY_PROOF:FAIL --@PREDICATE_CHECK:FAIL
      else
         return X.I;--@INIT_BY_PROOF:PASS --@PREDICATE_CHECK:PASS
      end if;
   end Get;

   function Read (X : R2) return Boolean is (True);

   function No_Read (X : R2) return Boolean is (True) with
     Relaxed_Initialization => X;

   --  Test checks on updates

   X : R2 with Relaxed_Initialization;
   V : Boolean;
begin
   --  R2 can be updated field by field
   if Rand (1) then
      X.H := ((C => 0), (C => 1));
      X.I := ((C => 2), (C => 3));
      V := Read (X); --@INIT_BY_PROOF:PASS

   --  R1 cannot as it has a predicate
   elsif Rand (2) then
      X.H.F := (C => 1);  --@PREDICATE_CHECK:FAIL  --@INIT_BY_PROOF:FAIL

   --  Complete initialization will be checked when reading a value of type R2
   elsif Rand (3) then
      X.I := ((C => 2), (C => 3));
      V := Read (X);  --@INIT_BY_PROOF:FAIL

   --  No checks are emitted if no reads are performed
   elsif Rand (4) then
      X.I := ((C => 2), (C => 3));
      V := No_Read (X);  --@INIT_BY_PROOF:NONE
   elsif Rand (5) then
      X.I := ((C => 2), (C => 3));
      P (X);  --@PRECONDITION:FAIL @INIT_BY_PROOF:NONE
   elsif Rand (6) then
      Q (X);  --@INIT_BY_PROOF:NONE

   --  An initialized object of type R1 can still be updated field by field
   elsif Rand (7) then
      X.H := ((C => 0), (C => 2));
      X.H.G := (C => 1);  --@PREDICATE_CHECK:PASS
   elsif Rand (8) then
      X.H := ((C => 0), (C => 1));
      X.H.G := (C => 0);  --@PREDICATE_CHECK:FAIL

   --  Aggregates of type R2 can be partially initialized
   elsif Rand (9) then
      X := R2'(H => R1'((C => 0), (C => 2)), I => R1'((C => 2), (C => 3))); --@PREDICATE_CHECK:PASS
      V := Read (X); --@INIT_BY_PROOF:PASS
   elsif Rand (10) then
      X := (X with delta H => R1'((C => 0), (C => 1))); --@PREDICATE_CHECK:PASS
      V := Read (X);  --@INIT_BY_PROOF:FAIL
   elsif Rand (11) then
      X.I := R2'(X with delta H => R1'((C => 0), (C => 1))).H; --@PREDICATE_CHECK:PASS
      V := Read (X);  --@INIT_BY_PROOF:FAIL
   elsif Rand (12) then
      X.I := R2'(X with delta H => R1'((C => 0), (C => 1))).I; --@INIT_BY_PROOF:FAIL --@PREDICATE_CHECK:FAIL
   elsif Rand (13) then
      X := (X with delta H => R1'((C => 0), (C => 1))); --@PREDICATE_CHECK:PASS
      X.I := R2'(X with delta H => R1'((C => 0), (C => 1))).H; --@PREDICATE_CHECK:PASS
      V := Read (X);  --@INIT_BY_PROOF:PASS

   --  Aggregates of type R1 cannot

   elsif Rand (14) then
      declare
         H : Holder with Relaxed_Initialization;
      begin
         X.H := (F => H, G => (C => 0)); --@INIT_BY_PROOF:FAIL
      end;

   --  In delta aggregates, even the prefix shall be initialized as it is read

   elsif Rand (15) then
      X.H := (X.H with delta F => (C => 0)); --@INIT_BY_PROOF:FAIL
   elsif Rand (16) then
      X.H := ((C => 0), (C => 1));
      X.H := (X.H with delta G => (C => 0)); --@PREDICATE_CHECK:FAIL
   elsif Rand (17) then
      X.H := ((C => 0), (C => 1));
      declare
         H : Holder with Relaxed_Initialization;
      begin
         X.H := (X.H with delta G => H); --@INIT_BY_PROOF:FAIL
      end;
   end if;
end Test_Predicates;
