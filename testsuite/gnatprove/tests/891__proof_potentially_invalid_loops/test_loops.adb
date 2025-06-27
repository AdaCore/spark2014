procedure Test_Loops with SPARK_Mode is

   type R is record
      I : Positive;
   end record;

   type RR is record
      C : R;
   end record;

   procedure Test_Loop_1 (X : out R) with
     Potentially_Invalid => X,
     Global => null;

   procedure Test_Loop_1 (X : out R) is
   begin
      X := (I => 12);
      for K in 1 .. 100 loop
         X.I := X.I / 2 + 1;  --  @VALIDITY_CHECK:PASS
      end loop;
   end Test_Loop_1;

   procedure Test_Loop_2 (X : in out R) with
     Potentially_Invalid => X,
     Global => null;

   procedure Test_Loop_2 (X : in out R) is
   begin
      for K in 1 .. 100 loop
         X.I := X.I / 2 + 1; --  @VALIDITY_CHECK:FAIL
      end loop;
   end Test_Loop_2;

   procedure Test_Loop_3 (X : out R; Y : R) with
     Potentially_Invalid => (X, Y),
     Global => null;

   procedure Test_Loop_3 (X : out R; Y : R) is
   begin
      X := (I => 12);
      for K in 1 .. 100 loop
         if K = 1 then
            X := Y;
         else
            X.I := X.I / 2 + 1; --  @VALIDITY_CHECK:FAIL
         end if;
      end loop;
   end Test_Loop_3;

   procedure Test_Loop_4 (X : out R; Y : R) with
     Potentially_Invalid => X,
     Global => null;

   procedure Test_Loop_4 (X : out R; Y : R) is
   begin
      X := (I => 12);
      for K in 1 .. 100 loop
         if K = 1 then
            X := Y;
         else
            X.I := X.I / 2 + 1; --  @VALIDITY_CHECK:PASS
         end if;
      end loop;
   end Test_Loop_4;

   procedure Test_Loop_5 (X : in out RR; Y : R) with
     Potentially_Invalid => (X, Y),
     Pre => X'Valid_Scalars,
     Post => X'Valid_Scalars; --  @POSTCONDITION:FAIL

   procedure Test_Loop_5 (X : in out RR; Y : R) is
   begin
      for K in 1 .. 100 loop
         X.C := Y;
      end loop;
   end Test_Loop_5;

   procedure Test_Loop_6 (X : in out RR) with
     Potentially_Invalid => X,
     Pre => X'Valid_Scalars,
     Post => X'Valid_Scalars; --  @POSTCONDITION:FAIL

   procedure Test_Loop_6 (X : in out RR) is
      procedure Set (Y : in out R) with
        Always_Terminates,
        Import,
        Potentially_Invalid => Y,
        Global => null;
   begin
      for K in 1 .. 100 loop
         Set (X.C);
      end loop;
   end Test_Loop_6;

   procedure Test_Loop_7 (X : in out RR) with
     Potentially_Invalid => X,
     Pre => X'Valid_Scalars,
     Post => X'Valid_Scalars; --  @POSTCONDITION:FAIL

   procedure Test_Loop_7 (X : in out RR) is
      procedure Set with
        Always_Terminates,
        Import,
        Global => (In_Out => X);
   begin
      for K in 1 .. 100 loop
         Set;
      end loop;
   end Test_Loop_7;

   procedure Test_Loop_9 with Global => null;

   procedure Test_Loop_9 is
      function Init return Positive with Import,
        Global => null,
        Potentially_Invalid => Init'Result;
   begin
      for K in 1 .. 100 loop
         declare
            X : Positive := Init with Potentially_Invalid;
         begin
            if K mod 2 = 1 then
               X := 1;
            end if;
            pragma Loop_Invariant (True);
            pragma Assert (X'Valid); --  @ASSERT:FAIL
         end;
      end loop;
   end Test_Loop_9;

begin
   null;
end Test_Loops;
