procedure Test with SPARK_Mode is

   function Rand return Boolean with
     Global => null,
     Import;

   type R (D : Integer := 1) is record
      A, B : Integer;
   end record;

   subtype S is R (1);

   procedure Q_1 (X : out R; B : out Boolean) with
     Pre     => not X'Constrained,
     Depends => (B => X, X => null);
   --  The output value of B depends on the input value of X, X's discriminants
   --  need to be written prior to the call to avoid missing dependencies.

   procedure Q_1 (X : out R; B : out Boolean) is
   begin
      B := X.D = 0; -- @INIT_BY_PROOF:NONE
      X := (D => 12, others => 0);
   end Q_1;

   procedure Q_2 (X : out R; B : out Boolean) with
     Relaxed_Initialization => X,
     Pre     => not X'Constrained,
     Depends => (B => null, X => null);
   --  The output value of B does not impact any output, it is fine if it is
   --  not written before the call.

   procedure Q_2 (X : out R; B : out Boolean) is
   begin
      X := (D => 12, others => 0);
      B := True;
   end Q_2;

   type RR is record
      F : R;
   end record;

   procedure P_1 (X : out RR; B : out Boolean) with
     Depends => (B => null, X => null);

   procedure P_1 (X : out RR; B : out Boolean) is
   begin
      B := X.F.D = 0; --  @INITIALIZED:CHECK
      X := (F => (D => 12, others => 0));
   end P_1;

   procedure P_2 (X : out RR; B : out Boolean) with
     Depends => (B => null, X => null),
     Relaxed_Initialization => X;

   procedure P_2 (X : out RR; B : out Boolean) is
   begin
      B := X.F.D = 0; -- @INIT_BY_PROOF:FAIL
      X := (F => (D => 12, others => 0));
   end P_2;

   procedure P_3 (X : out RR; B : out Boolean) with
     Depends => (B => null, X => null),
     Relaxed_Initialization => X;

   procedure P_3 (X : out RR; B : out Boolean) is
   begin
      Q_1 (X.F, B); -- @INIT_BY_PROOF:FAIL
   end P_3;

   type A is array (Integer range 1 .. 1) of R;

   procedure P_1 (X : out A; B : out Boolean) with
     Depends => (B => null, X => null);

   procedure P_1 (X : out A; B : out Boolean) is
   begin
      B := X (1).D = 0; --  Flow analysis should emit an initialization check here
      X := (1 => (D => 12, others => 0));
   end P_1;

   procedure P_2 (X : out A; B : out Boolean) with
     Depends => (B => null, X => null),
     Relaxed_Initialization => X;

   procedure P_2 (X : out A; B : out Boolean) is
   begin
      B := X (1).D = 0;  -- @INIT_BY_PROOF:FAIL
      X (1) := (D => 12, others => 0);
   end P_2;

   procedure P_3 (X : out A; B : out Boolean) with
     Depends => (B => null, X => null),
     Relaxed_Initialization => X;

   procedure P_3 (X : out A; B : out Boolean) is
   begin
      Q_1 (X (1), B);  -- @INIT_BY_PROOF:FAIL
      B := B and then X (1).D = 1;  -- @INIT_BY_PROOF:PASS
   end P_3;

   procedure P_4 (X : out A; B : out Boolean) with
     Depends => (B => null, X => null),
     Relaxed_Initialization => X;

   procedure P_4 (X : out A; B : out Boolean) is
   begin
      Q_2 (X (1), B); --  Could remove the initialization check here, Q_2 has a Depends contract stating that X => null
      B := B and then X (1).D = 1;  -- @INIT_BY_PROOF:PASS
   end P_4;

   --  Test that initialization checks are emitted on "for of" quantification
   --  over arrays.

   procedure P_5 (X : out A; B : out Boolean) with
     Depends => (B => null, X => null),
     Relaxed_Initialization => X;

   procedure P_5 (X : out A; B : out Boolean) is
   begin
      B := (for all E of X => E.D = 1);  -- @INIT_BY_PROOF:FAIL
      X (1) := (D => 12, others => 0);
   end P_5;

   --  Two procedures swapping their parameters but X (1) does not have
   --  initialized discriminants while Y has. An initialization check should
   --  fail.

   procedure P_6 (X : out A; Y : out R) with
     Pre => not Y'Constrained,
     Relaxed_Initialization => (X, Y);

   procedure P_6 (X : out A; Y : out R) is
      T : constant R := Y with Relaxed_Initialization;
   begin
      Y := X (1);  -- @INIT_BY_PROOF:FAIL
      X (1) := T;
   end P_6;

   procedure P_7 (X : out A; Y : out R) with
     Pre => not Y'Constrained,
     Relaxed_Initialization => (X, Y);

   procedure P_7 (X : out A; Y : out R) is
      T : constant R := X (1) with Relaxed_Initialization;  -- @INIT_BY_PROOF:FAIL
   begin
      X (1) := Y;
      Y := T;
   end P_7;

   --  Conversion and membersip tests wrt a constrained subtype require
   --  initialization checks.

   procedure P_8 (X : out A; B : in out Boolean) with
     Pre => (if B then X (1) in S),  -- @INIT_BY_PROOF:FAIL
     Relaxed_Initialization => X;

   procedure P_8 (X : out A; B : in out Boolean) is
   begin
      Q_1
        (S           -- @INIT_BY_PROOF:NONE
           (X (1)),  -- @INIT_BY_PROOF:FAIL
         B);
   end P_8;

begin
   null;
end Test;
