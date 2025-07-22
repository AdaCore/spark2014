procedure Test_Basic with spark_mode is

   type R is record
      I : Positive;
   end record;

   type RR is record
      C1, C2 : R;
   end record;

   function Read return R with
     Global => null,
     Potentially_Invalid => Read'Result,
     Import;

   procedure Test_Assign (X1, X2, X3, X4 : R) with
     Potentially_Invalid => (X1, X3, X4),
     Pre => X1'Valid_Scalars;

   procedure Test_Assign (X1, X2, X3, X4 : R) is
      Y : R with Potentially_Invalid;
   begin
      Y := X1;
      pragma Assert (Y'Valid_Scalars);
      Y := X2;
      pragma Assert (Y'Valid_Scalars);
      Y := R (X3);                     --  @VALIDITY_CHECK:FAIL
      pragma Assert (Y'Valid_Scalars);
      Y := X4;
      pragma Assert (Y'Valid_Scalars); --  @ASSERT:FAIL
   end Test_Assign;

   procedure Set (X : R; Y : out R) with
     Potentially_Invalid => (X, Y),
     Post => Y'Valid_Scalars = X'Valid_Scalars;
   procedure Set (X : R; Y : out R) is
   begin
      Y := X;
   end Set;

   procedure Test_Call (X1, X2, X3, X4 : R) with
     Potentially_Invalid => (X1, X3, X4),
     Pre => X1'Valid_Scalars;

   procedure Test_Call (X1, X2, X3, X4 : R) is

      Y : R with Potentially_Invalid;
   begin
      Set (X1, Y);
      pragma Assert (Y'Valid_Scalars);
      Set (X2, Y);
      pragma Assert (Y'Valid_Scalars);
      Set (R (X3), Y);                 --  @VALIDITY_CHECK:FAIL
      pragma Assert (Y'Valid_Scalars);
      Set (X4, Y);
      pragma Assert (Y'Valid_Scalars); --  @ASSERT:FAIL
   end Test_Call;

   procedure Test_Call_2 (X1, X2, X3 : R) with
     Potentially_Invalid => (X1, X3),
     Pre => X1'Valid_Scalars;

   procedure Test_Call_2 (X1, X2, X3 : R) is

      Y : R;
   begin
      Set (X1, Y);
      Set (X2, Y);
      Set (X3, Y);  --  @VALIDITY_CHECK:FAIL
      pragma Assert (Y'Valid_Scalars);
   end Test_Call_2;

   procedure Set_2 (X : R; Y : out R) with Global => null;
   procedure Set_2 (X : R; Y : out R) is
   begin
      Y := X;
   end Set_2;

   procedure Test_Call_3 (X1, X2, X3, X4 : R) with
     Potentially_Invalid => (X1, X3),
     Pre => X1'Valid_Scalars;

   procedure Test_Call_3 (X1, X2, X3, X4 : R) is
      Y : R with Potentially_Invalid;
   begin
      Y := X4;
      Set_2 (X1, Y);
      pragma Assert (Y'Valid_Scalars);
      Set_2 (X2, Y);
      pragma Assert (Y'Valid_Scalars);
      Set_2 (X3, Y);                     --  @VALIDITY_CHECK:FAIL
      pragma Assert (Y'Valid_Scalars);
   end Test_Call_3;

   procedure Test_Declare (X1, X2, X3, X4 : R) with
     Potentially_Invalid => (X1, X3, X4),
     Pre => X1'Valid_Scalars;

   procedure Test_Declare (X1, X2, X3, X4 : R) is
   begin
      declare
         Y : R := X1 with Potentially_Invalid;
      begin
         pragma Assert (Y'Valid_Scalars);
      end;
      declare
         Y : R := X2 with Potentially_Invalid;
      begin
         pragma Assert (Y'Valid_Scalars);
      end;
      declare
         Y : R := R (X3) with Potentially_Invalid;  --  @VALIDITY_CHECK:FAIL
      begin
         pragma Assert (Y'Valid_Scalars);
      end;
      declare
         Y : R := X4 with Potentially_Invalid;
      begin
         pragma Assert (Y'Valid_Scalars); --  @ASSERT:FAIL
      end;
   end Test_Declare;

   procedure Test_Declare_Cst (X1, X2, X3, X4 : R) with
     Potentially_Invalid => (X1, X3, X4),
     Pre => X1'Valid_Scalars;

   procedure Test_Declare_Cst (X1, X2, X3, X4 : R) is
   begin
      declare
         Y : constant R := X1 with Potentially_Invalid;
      begin
         pragma Assert (Y'Valid_Scalars);
      end;
      declare
         Y : constant R := X2 with Potentially_Invalid;
      begin
         pragma Assert (Y'Valid_Scalars);
      end;
      declare
         Y : constant R := R (X3) with Potentially_Invalid; --  @VALIDITY_CHECK:FAIL
      begin
         pragma Assert (Y'Valid_Scalars);
      end;
      declare
         Y : constant R := X4 with Potentially_Invalid;
      begin
         pragma Assert (Y'Valid_Scalars); --  @ASSERT:FAIL
      end;
   end Test_Declare_Cst;

   C1 : constant R := (I => 12) with Potentially_Invalid;

   C2 : constant R := Read with Potentially_Invalid;

   procedure Test_Assume_Constant with Global => null;

   procedure Test_Assume_Constant is
   begin
      pragma Assert (C1'Valid_Scalars);
      pragma Assert (C2'Valid_Scalars); --  @ASSERT:FAIL
   end Test_Assume_Constant;

   procedure Test_Old is

      procedure Test_Old_1  (X1, X2 : in out R) with
        Potentially_Invalid => (X1, X2),
        Pre => X1'Valid_Scalars,
        Post => X1'Old'Valid_Scalars;

      procedure Test_Old_1  (X1, X2 : in out R) is
      begin
         X1 := X2;
      end Test_Old_1;

      procedure Test_Old_2  (X : in out R) with
        Potentially_Invalid => X,
        Post => X'Old'Valid_Scalars; --  @POSTCONDITION:FAIL

      procedure Test_Old_2  (X : in out R) is
      begin
         X := (I => 12);
      end Test_Old_2;

      procedure Test_Old_3  (X : in out R) with
        Potentially_Invalid => X,
        Post => X.I'Old'Valid_Scalars; --  @VALIDITY_CHECK:FAIL

      procedure Test_Old_3  (X : in out R) is
      begin
         X := (I => 12);
      end Test_Old_3;

      function F (X : R) return Boolean is (True);

      procedure Test_Old_4  (X : in out R) with
        Potentially_Invalid => X,
        Post => F (X'Old); --  @VALIDITY_CHECK:FAIL

      procedure Test_Old_4  (X : in out R) is
      begin
         X := (I => 12);
      end Test_Old_4;

      procedure Test_Old_5  (X : in out RR) with
        Potentially_Invalid => X,
        Post => X.C1'Old'Valid_Scalars; --  @POSTCONDITION:FAIL

      procedure Test_Old_5  (X : in out RR) is
      begin
         X.C1 := (I => 12);
      end Test_Old_5;

      procedure Test_Old_6  (X : in out RR) with
        Potentially_Invalid => X,
        Post => F (X.C1'Old); --  @VALIDITY_CHECK:FAIL

      procedure Test_Old_6  (X : in out RR) is
      begin
         X.C1 := (I => 12);
      end Test_Old_6;
   begin
      null;
   end Test_Old;

   procedure Test_Loop_Entry is

      procedure Test_Loop_Entry_1  (X1, X2 : in out R) with
        Potentially_Invalid => (X1, X2),
        Pre => X1'Valid_Scalars;

      procedure Test_Loop_Entry_1  (X1, X2 : in out R) is
      begin
         for I in 1 .. 10 loop
            pragma Loop_Invariant (X1'Loop_Entry'Valid_Scalars);
            X1 := X2;
         end loop;
      end Test_Loop_Entry_1;

      procedure Test_Loop_Entry_2  (X1, X2 : in out R) with
        Potentially_Invalid => (X1, X2),
        Pre => X1'Valid_Scalars;

      procedure Test_Loop_Entry_2  (X1, X2 : in out R) is
      begin
         for I in 1 .. 10 loop
            pragma Loop_Invariant (X2'Loop_Entry'Valid_Scalars); --  @LOOP_INVARIANT_INIT:FAIL
            X2 := (I => 12);
         end loop;
      end Test_Loop_Entry_2;

      procedure Test_Loop_Entry_3  (X1, X2 : in out R) with
        Potentially_Invalid => (X1, X2),
        Pre => X1'Valid_Scalars;

      procedure Test_Loop_Entry_3  (X1, X2 : in out R) is
      begin
         for I in 1 .. 10 loop
            pragma Loop_Invariant (X2.I'Loop_Entry'Valid_Scalars); --  @VALIDITY_CHECK:FAIL
            X2 := (I => 12);
         end loop;
      end Test_Loop_Entry_3;

      procedure Test_Loop_Entry_4  (X1, X2 : in out R) with
        Potentially_Invalid => (X1, X2),
        Pre => X1'Valid_Scalars;

      procedure Test_Loop_Entry_4  (X1, X2 : in out R) is
      begin
         for I in 1 .. 10 loop
            pragma Loop_Invariant (X2'Loop_Entry = (I => 12)); --  @VALIDITY_CHECK:FAIL
            X2 := (I => 12);
         end loop;
      end Test_Loop_Entry_4;
   begin
      null;
   end Test_Loop_Entry;

   --  Reads of global objects in functions

   V : R with Potentially_Invalid;

   function Read_V return R with
     Pre => V'Valid_Scalars,
     Global => V
   is
   begin
      return V;
   end Read_V;

   function Read_V_Bad return R with
     Global => V
   is
   begin
      return V; --  @VALIDITY_CHECK:FAIL
   end Read_V_Bad;

   function Read_V_Inv return R with
     Potentially_Invalid => Read_V_Inv'Result,
     Global => V
   is
   begin
      return V;
   end Read_V_Inv;

   --  Test for updates into components of potentially invalid objects

   procedure Test_Partial_Updates (X1, X2, X3, X4 : in out RR; Y1, Y2 : R) with
     Potentially_Invalid => (X1, X2, X3, X4, Y1, Y2),
     Pre => X1'Valid_Scalars and X3'Valid_Scalars;

   procedure Test_Partial_Updates (X1, X2, X3, X4 : in out RR; Y1, Y2 : R) is
     X2_Old : constant RR := X2 with Potentially_Invalid;
     X4_Old : constant RR := X4 with Potentially_Invalid;
   begin
      X1.C1 := Y1;
      pragma Assert (X1'Valid_Scalars = Y1'Valid_Scalars);
      X2.C1 := Y2;
      pragma Assert (if X2'Valid_Scalars then Y2'Valid_Scalars);
      pragma Assert (if X2'Valid_Scalars then X2_Old'Valid_Scalars); --  @ASSERT:FAIL
      Set (Y1, X3.C1);
      pragma Assert (X3'Valid_Scalars = Y1'Valid_Scalars);
      Set (Y2, X4.C1);
      pragma Assert (if X4'Valid_Scalars then Y2'Valid_Scalars);
      pragma Assert (if X4'Valid_Scalars then X4_Old'Valid_Scalars); --  @ASSERT:FAIL
   end Test_Partial_Updates;

   --  Test for havoc of parameters on exceptional exits

   E : exception;

   procedure Raise_E (X : in out R) with
     Exceptional_Cases => (E => True),
     Potentially_Invalid => X,
     Post => X'Valid_Scalars;

   procedure Raise_E (X : in out R) is
   begin
      raise E;
   end Raise_E;

   procedure Exp_Store (X : in out R) with
     Exceptional_Cases => (E => True),
     Potentially_Invalid => X,
     Pre => X'Valid_Scalars
   is
   begin
      Raise_E (X);
   exception
      when E =>
         pragma Assert (X'Valid_Scalars);  --  @ASSERT:FAIL
   end Exp_Store;
begin
   null;
end;
