procedure Test_Relaxed_Parameters
  with
    SPARK_Mode => On
is

   E : exception;

   type R is record
      F, G : Integer;
   end record with
     Predicate => F < G;

   procedure P (X : aliased out R) with
     Relaxed_Initialization => X,
     No_Return,
     Exceptional_Cases => (E => True);

   procedure P (X : aliased out R) is
   begin
      raise E;
   end P;

   procedure Call_P (X : aliased out R) with
     No_Return,
     Exceptional_Cases => (E => True);

   procedure Call_P (X : aliased out R) is
   begin
      P (X); --@INIT_BY_PROOF:FAIL
   end Call_P;

   procedure Q (X : aliased out R) with
     Relaxed_Initialization => X,
     No_Return,
     Exceptional_Cases => (E => X'Initialized);

   procedure Q (X : aliased out R) is
   begin
      X := (15, 16);
      raise E;
   end Q;

   procedure Call_Q (X : aliased out R) with
     No_Return,
     Exceptional_Cases => (E => True);

   procedure Call_Q (X : aliased out R) is
   begin
      Q (X); --@INIT_BY_PROOF:PASS
   end Call_Q;

begin
   null;
end;
