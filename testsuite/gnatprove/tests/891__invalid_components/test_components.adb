procedure Test_Components with SPARK_Mode is
   type RD (D : Natural) is record
      F1, F2 : Natural;
   end record;

   subtype R is RD (0);

   type UA is array (Positive range <>) of R;
   subtype A is UA (1 .. 2);
   subtype S is UA (1 .. 5);

   type RR (D : Natural) is record
      G1 : RD (D);
      G2 : UA (1 .. D);
   end record;

   procedure Test_Access_OK is
      procedure Test_R (X : in out R) with
        Potentially_Invalid => X,
        Pre => X.F1'Valid;

      procedure Test_R (X : in out R) is
         I : Integer;
      begin
         pragma Assert (X.F1'Valid);
         I := X.F1;
         pragma Assert (X.F2'Valid); -- @ASSERT:FAIL
      end Test_R;

      procedure Test_A (X : in out A) with
        Potentially_Invalid => X,
        Pre => X (1)'Valid_Scalars;

      procedure Test_A (X : in out A) is
         I : Integer;
      begin
         pragma Assert (X (1).F1'Valid);
         I := X (1).F2;
         pragma Assert (X (2)'Valid_Scalars); -- @ASSERT:FAIL
      end Test_A;

      procedure Test_S (X : in out S) with
        Potentially_Invalid => X,
        Pre => X (1 .. 3)'Valid_Scalars;

      procedure Test_S (X : in out S) is
         I : A;
      begin
         I := X (2 .. 3);
         pragma Assert (X (1 .. 2)'Valid_Scalars);
         pragma Assert (X (3 .. 5)'Valid_Scalars); -- @ASSERT:FAIL
      end Test_S;

      procedure Test_RR (X : in out RR) with
        Potentially_Invalid => X,
        Pre => X.G1.F1'Valid and (if X.D >= 1 then X.G2 (1)'Valid_Scalars);

      procedure Test_RR (X : in out RR) is
         I : Integer;
      begin
         pragma Assert (X.G1.F1'Valid);
         I := X.G1.F1;
         if X.D >= 1 then
            pragma Assert (X.G2 (1).F1'Valid);
            I := X.G2 (1).F2;
         end if;
         pragma Assert (X.G1'Valid_Scalars); -- @ASSERT:FAIL
         pragma Assert (if X.D >= 2 then X.G2 (2)'Valid_Scalars); -- @ASSERT:FAIL
      end Test_RR;
   begin
      null;
   end;

   procedure Test_Access_Bad is
      procedure Test_R (X : in out R) with
        Potentially_Invalid => X,
        Post => True;

      procedure Test_R (X : in out R) is
         I : Integer;
      begin
         pragma Assert (X.F1'Valid); -- @ASSERT:FAIL
         I := X.F2; -- @VALIDITY_CHECK:FAIL
      end Test_R;

      procedure Test_A (X : in out A) with
        Potentially_Invalid => X,
        Post => True;

      procedure Test_A (X : in out A) is
         I : Integer;
      begin
         pragma Assert (X (1).F1'Valid); -- @ASSERT:FAIL
         I := X (1).F2; -- @VALIDITY_CHECK:FAIL
      end Test_A;

      procedure Test_S (X : in out S) with
        Potentially_Invalid => X,
        Post => True;

      procedure Test_S (X : in out S) is
         I : A;
      begin
         I := X (1 .. 2); -- @VALIDITY_CHECK:FAIL
         pragma Assert (X (3 .. 5)'Valid_Scalars); -- @ASSERT:FAIL
      end Test_S;

      procedure Test_RR (X : in out RR) with
        Potentially_Invalid => X,
        Post => True;

      procedure Test_RR (X : in out RR) is
         I : Integer;
      begin
         pragma Assert (X.G1.F1'Valid); -- @ASSERT:FAIL
         I := X.G1.F2; -- @VALIDITY_CHECK:FAIL
         if X.D >= 1 then
            pragma Assert (X.G2 (1).F1'Valid); -- @ASSERT:FAIL
            I := X.G2 (1).F2; -- @VALIDITY_CHECK:FAIL
         end if;
      end Test_RR;
   begin
      null;
   end;

   procedure Test_Write_OK is
      procedure Test_R (X : in out R) with
        Potentially_Invalid => X,
        Post => X'Valid_Scalars;

      procedure Test_R (X : in out R) is
      begin
         if not X'Valid_Scalars then
            X.F1 := 0;
         end if;
         if not X'Valid_Scalars then
            X.F2 := 0;
         end if;
      end Test_R;

      procedure Test_A (X : in out A) with
        Potentially_Invalid => X,
        Post => X'Valid_Scalars;

      procedure Test_A (X : in out A) is
      begin
         if not X'Valid_Scalars then
            X (1) := (0, 1, 2);
         end if;
         if not X'Valid_Scalars then
            X (2).F1 := 1;
            X (2).F2 := 1;
         end if;
      end Test_A;

      procedure Test_S (X : in out S) with
        Potentially_Invalid => X,
        Post => X'Valid_Scalars;

      procedure Test_S (X : in out S) is
         I : A;
      begin
         if not X (1 .. 2)'Valid_Scalars then
            X (1 .. 2) := (1 .. 2 => (0, 1, 1));
         end if;
         if not X (4 .. 5)'Valid_Scalars then
            X (4 .. 5) := (1 .. 2 => (0, 2, 2));
         end if;
         X (1 .. 3) (3) := (0, 1, 1);
      end Test_S;

      procedure Test_RR (X : in out RR) with
        Potentially_Invalid => X,
        Post => X'Valid_Scalars;

      procedure Test_RR (X : in out RR) is
      begin
         if not X'Valid_Scalars then
            X.G1.F1 := 1;
            X.G1.F2 := 1;
         end if;
         if not X'Valid_Scalars then
            for I in 1 .. X.D loop
               X.G2 (I).F1 := 1;
               X.G2 (I).F2 := 2;
               pragma Loop_Invariant (for all K in 1 .. I => X.G2 (K)'Valid_Scalars);
            end loop;
         end if;
      end Test_RR;
   begin
      null;
   end;

   procedure Test_Write_Bad is
      procedure Test_R (X : in out R) with
        Potentially_Invalid => X,
        Post => X'Valid_Scalars; -- @POSTCONDITION:FAIL

      procedure Test_R (X : in out R) is
      begin
         if not X'Valid_Scalars then
            X.F1 := 0;
         end if;
      end Test_R;

      procedure Test_A (X : in out A) with
        Potentially_Invalid => X,
        Post => X'Valid_Scalars; -- @POSTCONDITION:FAIL

      procedure Test_A (X : in out A) is
      begin
         if not X'Valid_Scalars then
            X (1) := (0, 1, 2);
         end if;
         if not X'Valid_Scalars then
            X (2).F1 := 1;
         end if;
      end Test_A;

      procedure Test_S (X : in out S) with
        Potentially_Invalid => X,
        Post => X'Valid_Scalars; -- @POSTCONDITION:FAIL

      procedure Test_S (X : in out S) is
         I : A;
      begin
         if not X (1 .. 2)'Valid_Scalars then
            X (1 .. 2) := (1 .. 2 => (0, 1, 1));
         end if;
         if not X (4 .. 5)'Valid_Scalars then
            X (4 .. 5) := (1 .. 2 => (0, 2, 2));
         end if;
      end Test_S;

      procedure Test_RR (X : in out RR) with
        Potentially_Invalid => X,
        Post => X'Valid_Scalars; -- @POSTCONDITION:FAIL

      procedure Test_RR (X : in out RR) is
      begin
         if not X'Valid_Scalars then
            X.G1.F1 := 1;
            X.G1.F2 := 1;
         end if;
         if not X'Valid_Scalars then
            for I in 2 .. X.D loop
               X.G2 (I).F1 := 1;
               X.G2 (I).F2 := 2;
               pragma Loop_Invariant (for all K in 2 .. I => X.G2 (K)'Valid_Scalars);
            end loop;
         end if;
      end Test_RR;
   begin
      null;
   end;
begin
   null;
end;
