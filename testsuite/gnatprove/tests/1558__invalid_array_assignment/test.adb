procedure Test with SPARK_Mode is
   type A is array (Positive range <>) of Positive;

   procedure Fill (X : out A) with
     Potentially_Invalid => X, Post => X'Valid_Scalars;

   procedure Fill (X : out A) is
   begin
      X := (others => 1);
   end Fill;

   procedure Copy (X : out A; Y : A) with
     Potentially_Invalid => (X, Y),
     Pre => X'Length = 2 and Y'Length = 2,
     Post => X (X'First)'Valid = Y (Y'First)'Valid
       and X (X'Last)'Valid = Y (Y'Last)'Valid;

   procedure Copy (X : out A; Y : A) is
   begin
      X := Y;
   end Copy;

   Calls : Natural := 0;

   function Make return A with
     Side_Effects, Global => (In_Out => Calls),
     Potentially_Invalid => Make'Result,
     Pre => Calls < Natural'Last,
     Post => Calls = Calls'Old + 1 and Make'Result'Length = 2
       and Make'Result'Valid_Scalars;

   function Make return A is
   begin
      Calls := Calls + 1;
      return (1 .. 2 => 1);
   end Make;

   procedure Assign (X : out A) with
     Potentially_Invalid => X,
     Pre => X'Length = 2 and Calls < Natural'Last,
     Post => X'Valid_Scalars and Calls = Calls'Old + 1;

   procedure Assign (X : out A) is
   begin
      X := Make;
   end Assign;

   X : A (5 .. 6) with Potentially_Invalid;
   Y : A (1 .. 2) with Import, Potentially_Invalid;
begin
   Fill (X);
   pragma Assert (X'Valid_Scalars);
   Assign (X);
   pragma Assert (Calls = 1);
   Copy (X, Y);
   pragma Assert (X (5)'Valid = Y (1)'Valid);
   pragma Assert (X (6)'Valid = Y (2)'Valid);
   pragma Assert (X'Valid_Scalars); -- @ASSERT:FAIL
end Test;
