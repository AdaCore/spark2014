procedure Test_Calls with SPARK_Mode is
   type R is record
      F : Positive;
   end record;

   type State is record
      Count : Natural;
   end record;

   function Read (Count : in out Natural) return R with
     Import, Side_Effects, Always_Terminates, Global => null,
     Potentially_Invalid => Read'Result,
     Pre => Count < Natural'Last,
     Post => Count = Count'Old + 1;

   function Read_Valid (Count : in out Natural) return R with
     Import, Side_Effects, Always_Terminates, Global => null,
     Potentially_Invalid => Read_Valid'Result,
     Pre => Count < Natural'Last,
     Post => Count = Count'Old + 1
       and then Read_Valid'Result'Valid_Scalars
       and then Read_Valid'Result.F = 7;

   procedure Check_Unknown with Global => null is
      S : State := (Count => 0);
      X : R;
   begin
      X := Read (S.Count); --  @VALIDITY_CHECK:FAIL
      pragma Assert (S.Count = 1);
   end Check_Unknown;

   procedure Check_Valid with Global => null is
      S : State := (Count => 0);
      X : R;
   begin
      X := Read_Valid (S.Count); --  @VALIDITY_CHECK:PASS
      pragma Assert (S.Count = 1);
      pragma Assert (X.F = 7);
   end Check_Valid;

   procedure Propagate_Unknown with Global => null is
      S : State := (Count => 0);
      X : R with Potentially_Invalid;
   begin
      X := Read (S.Count);
      pragma Assert (S.Count = 1);
      pragma Assert (X'Valid_Scalars); --  @ASSERT:FAIL
   end Propagate_Unknown;

   procedure Propagate_Valid with Global => null is
      S : State := (Count => 0);
      X : R with Potentially_Invalid;
   begin
      X := Read_Valid (S.Count);
      pragma Assert (S.Count = 1);
      pragma Assert (X'Valid_Scalars);
      pragma Assert (X.F = 7);
   end Propagate_Valid;

   function Forward (S : in out State) return R with
     Side_Effects, Potentially_Invalid => Forward'Result,
     Global => null,
     Pre => S.Count < Natural'Last,
     Post => S.Count = S.Count'Old + 1;

   function Forward (S : in out State) return R is
   begin
      return Read (S.Count);
   end Forward;

   function Read_Scalar (Count : in out Natural) return Positive with
     Import, Side_Effects, Always_Terminates, Global => null,
     Potentially_Invalid => Read_Scalar'Result,
     Pre => Count < Natural'Last,
     Post => Count = Count'Old + 1;

   procedure Check_Scalar with Global => null is
      S : State := (Count => 0);
   begin
      case Read_Scalar (S.Count) is --  @VALIDITY_CHECK:FAIL
         when 1 =>
            pragma Assert (S.Count = 1);
         when others =>
            null;
      end case;
   end Check_Scalar;

   procedure Propagate_Scalar with Global => null is
      S : State := (Count => 0);
      X : Positive with Potentially_Invalid;
   begin
      X := Read_Scalar (S.Count);
      pragma Assert (S.Count = 1);
      pragma Assert (X'Valid); --  @ASSERT:FAIL
   end Propagate_Scalar;

   function Read_Or_Fail (X : aliased in out R) return R with
     Import, Side_Effects, Always_Terminates, Global => null,
     Potentially_Invalid => Read_Or_Fail'Result,
     Post => X.F = 7,
     Exceptional_Cases => (Program_Error => X.F = 7);

   procedure Propagate_With_Exception with Global => null is
      type A is array (1 .. 2) of aliased R;
      Values : A := (others => (F => 1));
      X : R with Potentially_Invalid;
   begin
      X := Read_Or_Fail (Values (1));
      pragma Assert (Values (1).F = 7);
      pragma Assert (Values (2).F = 1);
      pragma Assert (X'Valid_Scalars); --  @ASSERT:FAIL
   exception
      when Program_Error =>
         pragma Assert (Values (1).F = 7);
         pragma Assert (Values (2).F = 1);
   end Propagate_With_Exception;
begin
   null;
end Test_Calls;
