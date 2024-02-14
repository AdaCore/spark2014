procedure P with SPARK_Mode is

   type R (D : Boolean := True) is record
      A, B : Integer;
   end record;

   procedure OK (X : out R; Y : out Boolean) with
     Depends => (X => null, Y => X),
     Relaxed_Initialization => X,
     Pre => X.D;

   procedure OK (X : out R; Y : out Boolean) is
   begin
      Y := X.D;
      X := (True, 12, 13);
   end OK;

   procedure Call_Ok with Global => null;

   procedure Call_Ok is
      X : R := (True, 1, 2) with Relaxed_Initialization;
      B : Boolean;
   begin
      Ok (X, B);
   end Call_Ok;

   procedure Bad (X : out R; Y : out Boolean) with
     Depends => ((X, Y) => null),
     Relaxed_Initialization => X,
     Pre => X'Initialized and not X'Constrained;

   procedure Bad (X : out R; Y : out Boolean) is
   begin
      Y := X.A < X.B;
      X := (True, 12, 13);
   end Bad;

   procedure Call_Bad with Global => null;

   procedure Call_Bad is
      X : R := (True, 1, 2) with Relaxed_Initialization;
      B : Boolean;
   begin
      Bad (X, B); -- @PRECONDITION:FAIL
   end Call_Bad;

   type Arr is array (Positive range <>) of Integer;

   procedure OK (X : out Arr; Y : out Boolean) with
     Depends => (X => X, Y => X),
     Relaxed_Initialization => X,
     Pre => X'First = 1;

   procedure OK (X : out Arr; Y : out Boolean) is
   begin
      Y := X'First = X'Last;
      X := (others => 14);
   end OK;

   procedure Call_Ok_Arr with Global => null;

   procedure Call_Ok_Arr is
      X : Arr := (1 => 12) with Relaxed_Initialization;
      B : Boolean;
   begin
      Ok (X, B);
   end Call_Ok_Arr;

   procedure Bad (X : out Arr; Y : out Boolean) with
     Depends => (X => X, Y => X),
     Relaxed_Initialization => X,
     Pre => X'Initialized;

   procedure Bad (X : out Arr; Y : out Boolean) is
   begin
      Y := (for all E of X => E = 0);
      X := (others => 13);
   end Bad;

   procedure Call_Bad_Arr with Global => null;

   procedure Call_Bad_Arr is
      X : Arr := (1 => 12) with Relaxed_Initialization;
      B : Boolean;
   begin
      Bad (X, B); -- @PRECONDITION:FAIL
   end Call_Bad_Arr;

begin
   null;
end P;
