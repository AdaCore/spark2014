procedure Test_Relaxed_Access_Call with SPARK_Mode is

   type Int_Acc is access Integer;

   type R_Int_Acc is new Int_Acc with Relaxed_Initialization;

   --  Check that OUT parameters are initialized at the end of procedures

   procedure P1 (X : out R_Int_Acc); -- @INIT_BY_PROOF:PASS

   procedure P1 (X : out R_Int_Acc) is
   begin
      X := new Integer'(15);
   end P1;

   procedure P2 (X : out R_Int_Acc; Y : Boolean); -- @INIT_BY_PROOF:FAIL

   procedure P2 (X : out R_Int_Acc; Y : Boolean) is
   begin
      if Y then
         X := new Integer'(15);
      end if;
   end P2;

   --  They are known to be initialized after the call

   procedure Call_P1 (Y : out Boolean) with Global => null;

   procedure Call_P1 (Y : out Boolean) is
      V : R_Int_Acc;
   begin
      P1 (V);
      Y := V = null; -- @INIT_BY_PROOF:PASS
   end Call_P1;

   --  Parts of composite types need not be initialized

   type R is record
      F : Int_Acc;
   end record;

   procedure P3 (X : out R; Y : Boolean) with -- @INIT_BY_PROOF:NONE
     Relaxed_Initialization => X;

   procedure P3 (X : out R; Y : Boolean) is
   begin
      if Y then
         X.F := new Integer'(15);
      end if;
   end P3;

   --  Partial exit is allowed on exceptional paths

   procedure P4 (X : aliased out R_Int_Acc; Y : Boolean) with -- @INIT_BY_PROOF:PASS
     Exceptional_Cases => (Program_Error => True);

   procedure P4 (X : aliased out R_Int_Acc; Y : Boolean) is
   begin
      if Y then
         X := new Integer'(15);
      else
         raise Program_Error;
      end if;
   end P4;

   procedure P5 (X : aliased out R_Int_Acc; Y : Boolean) with
     No_Return,
     Exceptional_Cases => (Program_Error => (if Y then X'Initialized)); -- @EXCEPTIONAL_CASE:PASS

   procedure P5 (X : aliased out R_Int_Acc; Y : Boolean) is
   begin
      if Y then
         X := new Integer'(13);
      end if;
      raise Program_Error;
   end P5;

   procedure Call_P5 (X : aliased out R_Int_Acc; Y : Boolean); -- @INIT_BY_PROOF:FAIL

   procedure Call_P5 (X : aliased out R_Int_Acc; Y : Boolean) is
   begin
      P5 (X, Y);
   exception
      when others => null;
   end Call_P5;

   --  Global output does not need to be initialized

   C : constant Int_Acc := new Integer'(0) with Relaxed_Initialization;

   V : Int_Acc with Relaxed_Initialization;

   procedure P6 (Y : Boolean) with
     Global => (Output => V);

   procedure P6 (Y : Boolean) is
   begin
      if Y then
         V := new Integer'(15);
      end if;
   end P6;

   procedure P7 (Y : out Boolean; B : Boolean) with
     Global => (Output => C), --  OK, global output does not need to be initialized
     Depends => (Y => null, C => B);

   procedure P7 (Y : out Boolean; B : Boolean) is
   begin
      Y := C = null;
      if B then
         C.all := 5;
      end if;
   end P7;

   --  Global output is not necessarily initialized after a call

   procedure Call_P6 (Y : in out Boolean) with
     Global => (Output => V);

   procedure Call_P6 (Y : in out Boolean) is
   begin
      P6 (Y);
      Y := V = null; -- @INIT_BY_PROOF:FAIL
   end Call_P6;

   --  Incorrect specification with 'Initialized on an OUT parameter in a
   --  precondition. The precondition should not be provable.

   procedure Bad (X : out R; Y : out Boolean) with
     Depends => ((X, Y) => null),
     Relaxed_Initialization => X,
     Pre => X'Initialized;

   procedure Bad (X : out R; Y : out Boolean) is
   begin
      Y := X.F = null;
      X.F := new Integer'(15);
   end Bad;

   procedure Call_Bad with Global => null;

   procedure Call_Bad is
      X : R with Relaxed_Initialization;
      B : Boolean;
   begin
      Bad (X, B); -- @PRECONDITION:FAIL
   end Call_Bad;

   --  Same with a global OUTPUT

   procedure Bad_2 (Y : out Boolean) with
     Global => (Output => V),
     Depends => ((V, Y) => null),
     Pre => V'Initialized;

   procedure Bad_2 (Y : out Boolean) is
   begin
      Y := V = null;
      V := new Integer'(15);
   end Bad_2;

   procedure Call_Bad_2 with Global => (Output => V);

   procedure Call_Bad_2 is
      B : Boolean;
   begin
      V := new Integer'(15);
      Bad_2 (B); -- @PRECONDITION:FAIL
   end Call_Bad_2;

   procedure Bad_3 (Y : out Boolean) with
     Global => (Output => C),
     Depends => ((C, Y) => null),
     Pre => C'Initialized;

   procedure Bad_3 (Y : out Boolean) is
   begin
      Y := C.all = 1;
      C.all := 15;
   end Bad_3;

   procedure Call_Bad_3 with Global => (Output => C);

   procedure Call_Bad_3 is
      B : Boolean;
   begin
      C.all := 1;
      Bad_3 (B); -- @PRECONDITION:FAIL
   end Call_Bad_3;

begin
   null;
end Test_Relaxed_Access_Call;
