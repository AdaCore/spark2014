procedure Test_Relaxed_Access_Params with SPARK_Mode is

   --  Test parameter passing

   type R (D : Integer) is record
      F : Integer;
   end record;

   type R_Access is access R;
   subtype S is R_Access (12);

   type R_Acc_Rel is new R_Access with Relaxed_Initialization;
   subtype S2 is R_Acc_Rel (12);

   --  The address of OUT parameters might not be initialized, the dependency is
   --  not properly tracked by flow.

   procedure P1 (X : out R_Acc_Rel; Y : out Boolean) with
     Depends => ((X, Y) => null); --  Flow does not complain here

   procedure P1 (X : out R_Acc_Rel; Y : out Boolean) is
   begin
      Y := X /= null; -- @INIT_BY_PROOF:FAIL
      Y := Y and then X in S2;
      X := new R'(3, 2);
   end P1;

   --  The same holds true for types with null exclusion whose constraints
   --  should not be depended on.

   procedure P2 (X : out not null R_Acc_Rel; Y : out Boolean) with
     Depends => ((X, Y) => null); --  Flow does not complain here

   procedure P2 (X : out not null R_Acc_Rel; Y : out Boolean) is
   begin
      Y := X /= null;
      Y := Y and then X in S2; -- @INIT_BY_PROOF:FAIL
      X := new R'(3, 2);
   end P2;

   --  For IN (OUT) parameters, the address is necessarily initialized. Its
   --  value is properly tracked by flow.

   procedure P3 (X : in out R_Acc_Rel; Y : out Boolean) with
     Depends => ((X, Y) => null, null => X); --  Flow complains here

   procedure P3 (X : in out R_Acc_Rel; Y : out Boolean) is
   begin
      Y := X /= null;
      Y := Y and then X in S2;
      X := new R'(3, 2);
   end P3;

   procedure P4 (X : in out not null R_Acc_Rel; Y : out Boolean) with
     Depends => ((X, Y) => null, null => X); --  Flow complains here

   procedure P4 (X : in out not null R_Acc_Rel; Y : out Boolean) is
   begin
      Y := X in S2;
      X := new R'(3, 2);
   end P4;

   --  The designated value might still not be initialized

   procedure P5 (X : in out not null R_Acc_Rel; Y : out Boolean) with
     Globals => null;

   procedure P5 (X : in out not null R_Acc_Rel; Y : out Boolean) is
   begin
      Y := X.F = 0; -- @INIT_BY_PROOF:FAIL
      X := new R'(3, 2);
   end P5;

   --  For components of composite objects, the value might not be initialized

   type H is record
      A : R_Access;
   end record;

   procedure P6 (X : out H; Y : in out Boolean) with
     Relaxed_Initialization => X;

   procedure P6 (X : out H; Y : in out Boolean) is
   begin
      if Y then
         Y := X.A = null; -- @INIT_BY_PROOF:FAIL
      else
         Y := X.A in S; -- @INIT_BY_PROOF:FAIL
      end if;
      X.A := new R'(3, 2);
   end P6;

   procedure P7 (X : in out H; Y : in out Boolean) with
     Relaxed_Initialization => X;

   procedure P7 (X : in out H; Y : in out Boolean) is
   begin
      if Y then
         Y := X.A = null; -- @INIT_BY_PROOF:FAIL
      else
         Y := X.A in S; -- @INIT_BY_PROOF:FAIL
      end if;
      X.A := new R'(3, 2);
   end P7;

   procedure P8 (X : H; Y : in out Boolean) with
     Relaxed_Initialization => X;

   procedure P8 (X : H; Y : in out Boolean) is
   begin
      if Y then
         Y := X.A = null; -- @INIT_BY_PROOF:FAIL
      else
         Y := X.A in S; -- @INIT_BY_PROOF:FAIL
      end if;
   end P8;

   --  Same for arrays

   type A is array (Positive range <>) of R_Access;

   procedure P9 (X : out A; Y : out Boolean) with
     Relaxed_Initialization => X,
     Depends => (X => X, Y => null);

   procedure P9 (X : out A; Y : out Boolean) is
   begin
      Y := (for all E of X => E = null); -- @INIT_BY_PROOF:FAIL
      X := (others => null);
   end P9;

   type A2 is array (Positive range <>) of not null R_Access;

   procedure P10 (X : out A2) with
     Relaxed_Initialization => X,
     Depends => (X => X);

   procedure P10 (X : out A2) is
   begin
      for I in X'Range loop
         X (I).all := (12, 14); -- @INIT_BY_PROOF:FAIL
      end loop;
   end P10;

   --  Check that top level initialization checks are introduced when a
   --  component access is passed as IN OUT parameter in an inner call.

   type H2 is record
      A : R_Acc_Rel;
   end record with Relaxed_Initialization;

   procedure P11 (X : out H2; Y : out Boolean);

   procedure P11 (X : out H2; Y : out Boolean) is
   begin
      P1 (X.A, Y); -- @INIT_BY_PROOF:NONE
   end P11;

   procedure P12 (X : in out H2; Y : out Boolean);

   procedure P12 (X : in out H2; Y : out Boolean) is
   begin
      P3 (X.A, Y); -- @INIT_BY_PROOF:FAIL
   end P12;

   --  Globals with relaxed initialization might always be uninitialized

   C : constant R_Access := new R'(12, 2) with Relaxed_Initialization;
   V : R_Access := new R'(12, 2) with Relaxed_Initialization;

   procedure Q1 with
     Global => (Output => V),
     Depends => (V => null); --  OK, here V is entirely initialized

   procedure Q1 is
   begin
      V := new R'(12, 4);
   end Q1;

   procedure Q2 with
     Global => (Output => V),
     Depends => (V => null);  --  Flow analysis does not complain here

   procedure Q2 is
   begin
      V.all := (12, 4); -- @INIT_BY_PROOF:FAIL
   end Q2;

   procedure Q3 with
     Global => (Output => C),
     Pre => C.D = 12,
     Depends => (C => null);  --  OK, the mutable part of C is entirely initialized

   procedure Q3 is
   begin
      C.all := (12, 4);
   end Q3;

   procedure Q4 with
     Global => (In_Out => V);

   procedure Q4 is
   begin
      V := new R'(12, 4);
   end Q4;

   procedure Q5 (Y : in out Boolean) with
     Global => (In_Out => V);

   procedure Q5 (Y : in out Boolean) is
   begin
      if Y then
         V.all := (12, 4); -- @INIT_BY_PROOF:FAIL
      else
         Y := V = null; -- @INIT_BY_PROOF:FAIL
      end if;
   end Q5;

   procedure Q6 (Y : in out Boolean) with
     Global => (In_Out => V),
     Pre => V /= null and then V.D = 12;
   --  We have no ways currently to state that the address of V should be
   --  considered to be initialized here.

   procedure Q6 (Y : in out Boolean) is
   begin
      if Y then
         V.all := (12, 4);
      else
         Y := V = null;
      end if;
   end Q6;


begin
   null;
end Test_Relaxed_Access_Params;
