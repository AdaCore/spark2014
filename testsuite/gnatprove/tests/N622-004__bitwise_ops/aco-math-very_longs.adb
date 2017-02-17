---------------------------------------------------------------------------
-- FILE    : aco-math-very_longs.adb
-- SUBJECT : Implementation of a Bit_Length bit integer package.
-- AUTHOR  : (C) Copyright 2014 by Peter C. Chapin
--
-- Please send comments or bug reports to
--
--      Peter C. Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

with ACO.Bit_Operations;
with ACO.Octet_Operations;
with ACO.Double_Octet_Operations;

package body ACO.Math.Very_Longs is
   use ACO.Bit_Operations;

   Digit_Bits : constant := 8;

   procedure Get_Hex_Digit(Raw_Digit : in Character; Digit : out ACO.Octet; Valid : out Boolean)
     with
       Depends => ((Digit, Valid) => Raw_Digit)
   is
   begin
      Valid := True;
      case Raw_Digit is
         when '0' .. '9' => Digit := (Character'Pos(Raw_Digit) - Character'Pos('0'));
         when 'A' .. 'F' => Digit := (Character'Pos(Raw_Digit) - Character'Pos('A')) + 10;
         when 'a' .. 'f' => Digit := (Character'Pos(Raw_Digit) - Character'Pos('a')) + 10;
         when others     =>
            Digit := 0;
            Valid := False;
      end case;
   end Get_Hex_Digit;


   -- Similar to ModAdd except that final carry is written to Carry.
   procedure ModAdd_And_Carry(L, R : in Very_Long; Result : out Very_Long; Carry : out ACO.Double_Octet)
     with
       Depends => (Result =>+ (L, R), Carry => (L, R)),
       Pre  => L.Octet_Length = R.Octet_Length,
       Post => Result.Octet_Length = L.Octet_Length
   is
      L_Digit : ACO.Double_Octet;
      R_Digit : ACO.Double_Octet;
      Sum     : ACO.Double_Octet;
   begin
      Result.Long_Digits := (others => 16#00#);
      Carry := 0;
      for I in L.Long_Digits'Range loop
         L_Digit := ACO.Double_Octet(L.Long_Digits(I));
         R_Digit := ACO.Double_Octet(R.Long_Digits(I));
         Sum     := L_Digit + R_Digit + Carry;
         Carry   := Double_Octet_Operations.Shift_Right(Sum, Digit_Bits);
         Result.Long_Digits(I) := TakeLSB_From16(Sum);
      end loop;
   end ModAdd_And_Carry;


   -- Similar to ModSubtract except that final borrow is written to Borrow.
   procedure ModSubtract_And_Borrow(L, R : in Very_Long; Result : out Very_Long; Borrow : out ACO.Double_Octet)
     with
       Depends => (Result =>+ (L, R), Borrow => (L, R)),
       Pre  => L.Octet_Length = R.Octet_Length,
       Post => Result.Octet_Length = L.Octet_Length
   is
      L_Digit    : ACO.Double_Octet;
      R_Digit    : ACO.Double_Octet;
      Difference : ACO.Double_Octet;
   begin
      Result.Long_Digits := (others => 16#00#);
      Borrow := 0;
      for I in L.Long_Digits'Range loop
         L_Digit    := ACO.Double_Octet(L.Long_Digits(I));
         R_Digit    := ACO.Double_Octet(R.Long_Digits(I));
         Difference := (L_Digit - R_Digit) - Borrow;
         if (Difference and 16#FF00#) /= 0 then
            Borrow := 1;
         else
            Borrow := 0;
         end if;
         Result.Long_Digits(I) := TakeLSB_From16(Difference);
      end loop;
   end ModSubtract_And_Borrow;


   ----------------------
   -- Visible Subprograms
   ----------------------

   --
   -- Constructors
   --

   function Make_From_Natural(Number : in Natural; Octet_Length : in Digit_Index_Type) return Very_Long is
      Result : Very_Long(Octet_Length);
      Temp   : Natural;
   begin
      Result.Long_Digits := (others => 16#00#);
      Temp := Number;
      for Index in Result.Long_Digits'Range loop
         Result.Long_Digits(Index) := ACO.Octet(Temp rem 256);
         Temp := Temp / 256;
      end loop;
      return Result;
   end Make_From_Natural;


   procedure Make_From_Hex_String(Number : in String; Result : out Very_Long; Valid : out Boolean)
   is
      Index        : Digit_Index_Type;
      String_Index : Positive;
      H_Digit      : ACO.Octet;
      L_Digit      : ACO.Octet;
      H_Okay       : Boolean;
      L_Okay       : Boolean;
   begin  -- Make_From_Hex_String
      Result.Long_Digits := (others => 16#00#);
      Valid := True;

      Index        := Result.Long_Digits'Last;
      String_Index := Number'First;
      loop
         pragma Loop_Invariant(String_Index = Positive(2 * (Result.Long_Digits'Last - Index) + 1));

         Get_Hex_Digit(Number(String_Index),     H_Digit, H_Okay);
         Get_Hex_Digit(Number(String_Index + 1), L_Digit, L_Okay);
         if not (H_Okay and L_Okay) then
            Valid := False;
            exit;
         end if;
         Result.Long_Digits(Index) := 16 * H_Digit + L_Digit;
         exit when Index = Result.Long_Digits'First;
         Index        := Index - 1;
         String_Index := String_Index + 2;
      end loop;
   end Make_From_Hex_String;


   --
   -- Relational Operators
   --

   function "<"(L, R : Very_Long) return Boolean is
      Result : Boolean := False;  -- Use this value if they are equal.
   begin
      for I in reverse L.Long_Digits'Range loop
         if L.Long_Digits(I) < R.Long_Digits(I) then
            Result := True;
            exit;
         end if;
         if L.Long_Digits(I) > R.Long_Digits(I) then
            Result := False;
            exit;
         end if;
      end loop;

      return Result;
   end "<";


   function "<="(L, R : Very_Long) return Boolean is
   begin
      return (L < R) or (L = R);
   end "<=";


   function ">"(L, R : Very_Long) return Boolean is
   begin
      return not (L <= R);
   end ">";


   function ">="(L, R : Very_Long) return Boolean is
   begin
      return not (L < R);
   end ">=";


   --function Is_Zero(Number : in Very_Long) return Boolean
   --  with Refined_Post => Is_Zero'Result = (for all I in Digits_Index_Type => Number(I) = 0)
   --is
   --begin
   --   return (for all I in Digits_Index_Type => Number(I) = 0);
   --end Is_Zero;

   --function Is_Zero(Number : Very_Long) return Boolean is (for all I in Digits_Index_Type => Number(I) = 0);

   --
   -- Arithmetic Operators
   --

   function ModAdd(L, R : Very_Long) return Very_Long is
      Result  : Very_Long(L.Octet_Length);
      L_Digit : ACO.Double_Octet;
      R_Digit : ACO.Double_Octet;
      Sum     : ACO.Double_Octet;
      Carry   : ACO.Double_Octet;
   begin
      Result.Long_Digits := (others => 16#00#);
      Carry := 0;
      for I in L.Long_Digits'Range loop
         L_Digit := ACO.Double_Octet(L.Long_Digits(I));
         R_Digit := ACO.Double_Octet(R.Long_Digits(I));
         Sum     := L_Digit + R_Digit + Carry;
         Carry   := Double_Octet_Operations.Shift_Right(Sum, Digit_Bits);
         Result.Long_Digits(I) := TakeLSB_From16(Sum);
      end loop;
      return Result;
   end ModAdd;


   function ModSubtract(L, R : Very_Long) return Very_Long is
      Result     : Very_Long(L.Octet_Length);
      L_Digit    : ACO.Double_Octet;
      R_Digit    : ACO.Double_Octet;
      Difference : ACO.Double_Octet;
      Borrow     : ACO.Double_Octet;
   begin
      Result.Long_Digits := (others => 16#00#);
      Borrow := 0;
      for I in L.Long_Digits'Range loop
         L_Digit    := ACO.Double_Octet(L.Long_Digits(I));
         R_Digit    := ACO.Double_Octet(R.Long_Digits(I));
         Difference := (L_Digit - R_Digit) - Borrow;
         if (Difference and 16#FF00#) /= 0 then
            Borrow := 1;
         else
            Borrow := 0;
         end if;
         Result.Long_Digits(I) := TakeLSB_From16(Difference);
      end loop;
      return Result;
   end ModSubtract;


   -- This is "Algorithm M" from Knuth's "The Art of Computer Programming, Volume 2: Seminumerical Algorithms" (third edition,
   -- published by Addison-Wesley, copyright 1998, pages 268-270).
   --
   function ModMultiply(L, R : Very_Long) return Very_Long is
      Result : Very_Long(L.Octet_Length);
      L_Digit : ACO.Double_Octet;
      R_Digit : ACO.Double_Octet;
      T_Digit : ACO.Double_Octet;
      Temp    : ACO.Double_Octet;
      Carry   : ACO.Double_Octet;
   begin
      -- Prepare Result's digit array.
      Result.Long_Digits := (others => 16#00#);

      -- Do the multiplication.
      for J in R.Long_Digits'Range loop
         Carry := 0;
         for I in L.Long_Digits'Range loop
            L_Digit := ACO.Double_Octet(L.Long_Digits(I));
            R_Digit := ACO.Double_Octet(R.Long_Digits(J));
            if I + J - 1 in Result.Long_Digits'Range then
               T_Digit := ACO.Double_Octet(Result.Long_Digits(I + J - 1));
               Temp    := (L_Digit * R_Digit) + T_Digit + Carry;
               Result.Long_Digits(I + J - 1) := TakeLSB_From16(Temp);
               Carry   := Double_Octet_Operations.Shift_Right(Temp, Digit_Bits);
            end if;
         end loop;
      end loop;
      return Result;
   end ModMultiply;


   function "*"(L, R : Very_Long) return Very_Long is
      Result  : Very_Long(L.Octet_Length + R.Octet_Length);
      L_Digit : ACO.Double_Octet;
      R_Digit : ACO.Double_Octet;
      T_Digit : ACO.Double_Octet;
      Temp    : ACO.Double_Octet;
      Carry   : ACO.Double_Octet;
   begin
      -- Prepare Result's digit array.
      Result.Long_Digits := (others => 16#00#);

      -- Do the multiplication.
      for J in R.Long_Digits'Range loop
         Carry := 0;
         for I in L.Long_Digits'Range loop
            L_Digit  := ACO.Double_Octet(L.Long_Digits(I));
            R_Digit  := ACO.Double_Octet(R.Long_Digits(J));
            T_Digit  := ACO.Double_Octet(Result.Long_Digits(I + J - 1));
            Temp     := (L_Digit * R_Digit) + T_Digit + Carry;
            Result.Long_Digits(I + J - 1) := TakeLSB_From16(Temp);
            Carry    := Double_Octet_Operations.Shift_Right(Temp, Digit_Bits);
         end loop;
         Result.Long_Digits(L.Octet_Length + J) := TakeLSB_From16(Carry);
      end loop;
      return Result;
   end "*";


   -- This is "Algorithm D" from Knuth's "The Art of Computer Programming, Volume 2: Seminumerical Algorithms" (third edition,
   -- published by Addison-Wesley, copyright 1998, pages 272-276).
   --
   procedure Divide(Dividend : in Very_Long; Divisor : in Very_Long; Quotient : out Very_Long; Remainder : out Very_Long) is

      -- Divisor has N digits. This subtype is used for values of N. The divisor must have at least one digit.
      subtype Divisor_Digits_Count_Type is Digit_Index_Type range 1 .. Divisor.Octet_Length;

      -- Dividend has 2*Divisor.Octet_Length = M + N digits. This subtype is used for values of M. Quotient has M + 1 digits.
      subtype Quotient_Digits_Count_Type is Digit_Index_Type range Divisor.Octet_Length .. 2*Divisor.Octet_Length - 1;

      -- This subtype is used for shift distances during the normalization and unnormalization steps.
      subtype Shift_Type is Natural range 0 .. 7;

      -- Refer to the document on multiprecision division to understand the names here.
      N               : Divisor_Digits_Count_Type;
      M               : Quotient_Digits_Count_Type;
      Shift_Distance  : Shift_Type;
      U               : Very_Long(2*Divisor.Octet_Length + 1);
      V               : Very_Long(Divisor.Octet_Length);
      J               : Digit_Index_Type;
      Q_Hat           : ACO.Double_Octet;
      Current_Borrow  : ACO.Double_Octet;

      -- Returns the digit index of the most significant (non-zero) digit of Number.
      function Get_MSD(Number : Very_Long) return Digit_Index_Type
        with
          Pre => not Is_Zero(Number),
          Post => Number.Long_Digits(Get_MSD'Result) /= 0 and
                 (for all I in Get_MSD'Result + 1 .. Number.Long_Digits'Last => Number.Long_Digits(I) = 0)
      is
         Digit_Index : Digit_Index_Type := 1;
      begin
         for I in Number.Long_Digits'Range loop
            if Number.Long_Digits(I) /= 0 then
               Digit_Index := I;
            end if;

            pragma Loop_Invariant(Number.Long_Digits(Digit_Index) /= 0 or (for some J in I + 1 .. Number.Long_Digits'Last => Number.Long_Digits(J) /= 0));
            pragma Loop_Invariant(if I > Digit_Index then (for all J in Digit_Index + 1 .. I => Number.Long_Digits(J) = 0));
         end loop;
         return Digit_Index;
      end Get_MSD;

      -- Returns the left shift distance required to move a 1 bit into the most significant position of Digit.
      function Get_Shift_Distance(Digit : ACO.Octet) return Shift_Type
        with
          Pre => Digit /= 0
      is
         Mask     : constant ACO.Octet := 16#01#;
         Distance : Shift_Type := 0;
      begin
         for I in Shift_Type loop
            if (Digit and Octet_Operations.Shift_Left(Mask, I)) /= 0 then
               Distance := Shift_Type'Last - I;
            end if;
         end loop;
         return Distance;
      end Get_Shift_Distance;

      -- Shifts Number to the left by Distance bits, putting the result into Result.
      procedure Full_Left_Shift(Number : in Very_Long; Result : out Very_Long; Distance : in Shift_Type)
        with
          Depends => (Result =>+ (Number, Distance)),
          Pre => Result.Octet_Length = Number.Octet_Length + 1
      is
         Old_Overflow  : ACO.Octet := 16#00#;
         New_Overflow  : ACO.Octet;
         Overflow_Mask : ACO.Octet;
      begin
         Result.Long_Digits := (others => 16#00#);
         Overflow_Mask := Octet_Operations.Shift_Left(16#FF#, 8 - Distance);
         for I in Number.Long_Digits'Range loop
            New_Overflow := Octet_Operations.Shift_Right(Number.Long_Digits(I) and Overflow_Mask, 8 - Distance);
            Result.Long_Digits(I) := Octet_Operations.Shift_Left(Number.Long_Digits(I), Distance);
            Result.Long_Digits(I) := Result.Long_Digits(I) or Old_Overflow;
            Old_Overflow := New_Overflow;
         end loop;
         Result.Long_Digits(Result.Long_Digits'Last) := Old_Overflow;
      end Full_Left_Shift;

      -- Shifts Number to the left by Distance bits. The final overflow is dropped (should be zero when used as below).
      procedure Left_Shift(Number : in out Very_Long; Distance : in Shift_Type)
        with
          Depends => (Number =>+ Distance)
      is
         Old_Overflow  : ACO.Octet := 16#00#;
         New_Overflow  : ACO.Octet;
         Overflow_Mask : ACO.Octet;
      begin
         Overflow_Mask := Octet_Operations.Shift_Left(16#FF#, 8 - Distance);
         for I in Number.Long_Digits'Range loop
            New_Overflow := Octet_Operations.Shift_Right(Number.Long_Digits(I) and Overflow_Mask, 8 - Distance);
            Number.Long_Digits(I) := Octet_Operations.Shift_Left(Number.Long_Digits(I), Distance);
            Number.Long_Digits(I) := Number.Long_Digits(I) or Old_Overflow;
            Old_Overflow := New_Overflow;
         end loop;
      end Left_Shift;

      -- Shifts Number to the right by Distance bits. The final overflow is dropped (should be zero (I think) when used as below).
      procedure Right_Shift(Number : in out Very_Long; Distance : in Shift_Type)
        with
          Depends => (Number =>+ Distance)
      is
         Old_Overflow  : ACO.Octet := 16#00#;
         New_Overflow  : ACO.Octet;
         Overflow_Mask : ACO.Octet;
      begin
         Overflow_Mask := Octet_Operations.Shift_Right(16#FF#, 8 - Distance);
         for I in reverse Number.Long_Digits'Range loop
            New_Overflow := Number.Long_Digits(I) and Overflow_Mask;
            Number.Long_Digits(I) := Octet_Operations.Shift_Right(Number.Long_Digits(I), Distance);
            Number.Long_Digits(I) := Number.Long_Digits(I) or Octet_Operations.Shift_Left(Old_Overflow, 8 - Distance);
            Old_Overflow := New_Overflow;
         end loop;
      end Right_Shift;

      procedure D3
        with
          Global => (Input => (J, N, U, V), Output => Q_Hat),
          Depends => (Q_Hat => (J, N, U, V))
      is
         Temporary_Digit : ACO.Double_Octet;
         R_Hat           : ACO.Double_Octet;
      begin
         Temporary_Digit := 256 * ACO.Double_Octet(U.Long_Digits(J + N - 1)) + ACO.Double_Octet(U.Long_Digits((J + N) - 2));
         Q_Hat := Temporary_Digit / ACO.Double_Octet(V.Long_Digits(N - 1));    -- Q_Hat has at most 9 bits.
         R_Hat := Temporary_Digit mod ACO.Double_Octet(V.Long_Digits(N - 1));  -- R_Hat has at most 8 bits.

         -- In the implementation here: http://www.hackersdelight.org/HDcode/divmnu.c.txt the test below is Q_Hat >= 256. Knuth's
         -- book clearly shows Q_Hat = 256 but perhaps that is a typo in Knuth's book.
         -- TODO: Find out what the correct test actually is.
         --
         if Q_Hat = 256 or Q_Hat * ACO.Double_Octet(V.Long_Digits(N - 2)) > 256 * R_Hat + ACO.Double_Octet(U.Long_Digits((J + N) - 3)) then
            Q_Hat := Q_Hat - 1;
            R_Hat := R_Hat + ACO.Double_Octet(V.Long_Digits(N - 1));
         end if;
         if R_Hat < 256 then
            -- This is the same test as above. Should it be moved into a separate subprogram?
            if Q_Hat = 256 or Q_Hat * ACO.Double_Octet(V.Long_Digits(N - 2)) > 256 * R_Hat + ACO.Double_Octet(U.Long_Digits((J + N) - 3)) then
               Q_Hat := Q_Hat - 1;
            end if;
         end if;
         -- At this point Q_Hat should be only an eight bit number.
      end D3;

      procedure D4
        with
          Global => (Input => (J, N, Q_Hat, V), Output => Current_Borrow, In_Out => U),
          Depends => (Current_Borrow => (J, N, Q_Hat, U, V), U => (J, N, Q_Hat, U, V))
      is
         Carry           : ACO.Double_Octet;
         Product         : ACO.Double_Octet;
         Temporary_Digit : ACO.Double_Octet;
         Future_Borrow   : ACO.Double_Octet;
      begin
         Carry := 0;
         Current_Borrow := 0;
         for Divisor_Index in Digit_Index_Type range 1 .. N loop
            Product := Q_Hat * ACO.Double_Octet(V.Long_Digits(Divisor_Index)) + Carry;
            Carry := Double_Octet_Operations.Shift_Right(Product, 8);

            Temporary_Digit := Product and 16#00FF#;
            if ACO.Double_Octet(U.Long_Digits(J + Divisor_Index - 1)) >= Temporary_Digit + Current_Borrow then
               Future_Borrow := 0;
            else
               Future_Borrow := 1;
            end if;
            U.Long_Digits(J + Divisor_Index - 1) :=
              ACO.Octet(((ACO.Double_Octet(U.Long_Digits(J + Divisor_Index - 1)) - Temporary_Digit) - Current_Borrow) and 16#00FF#);
            Current_Borrow := Future_Borrow;
         end loop;

         -- The last digit is handled as a special case.
         if ACO.Double_Octet(U.Long_Digits(J + N - 1)) >= Carry + Current_Borrow then
            Future_Borrow := 0;
         else
            Future_Borrow := 1;
         end if;
         U.Long_Digits(J + N - 1) := ACO.Octet(((ACO.Double_Octet(U.Long_Digits(J + N - 1)) - Carry) - Current_Borrow) and 16#00FF#);
         Current_Borrow := Future_Borrow;
      end D4;

      procedure D5
        with
          Global => (Input => (Current_Borrow, J, N, Q_Hat, V), In_Out => (Quotient, U)),
          Depends => (Quotient => (Current_Borrow, J, Q_Hat, Quotient), U => (Current_Borrow, J, N, U, V))
      is
         Carry : ACO.Double_Octet;
         Sum   : ACO.Double_Octet;
      begin
         Quotient.Long_Digits(J) := ACO.Octet(Q_Hat);  -- ??? This is where it really matters that Q_Hat be eight bits!
         if Current_Borrow /= 0 then

            -- D6 (Add Back)
            Quotient.Long_Digits(J) := Quotient.Long_Digits(J) - 1;
            Carry := 0;
            for Divisor_Index in Digit_Index_Type range 1 .. N loop
               Sum := ACO.Double_Octet(U.Long_Digits(J + Divisor_Index - 1)) + ACO.Double_Octet(V.Long_Digits(Divisor_Index)) + Carry;
               U.Long_Digits(J + Divisor_Index - 1) := TakeLSB_From16(Sum);
               Carry := Double_Octet_Operations.Shift_Right(Sum, 8);
            end loop;
            U.Long_Digits(J + N - 1) := U.Long_Digits(J + N - 1) + TakeLSB_From16(Carry);
         end if;
      end D5;

   begin  -- Divide
      Quotient.Long_Digits  := (others => 16#00#);
      Remainder.Long_Digits := (others => 16#00#);

      -- D0
      N := Get_MSD(Divisor) + 1;
      M := 48 - N;

      -- D1 (Normalize)
      Shift_Distance := Get_Shift_Distance(Divisor.Long_Digits(N - 1));
      Full_Left_Shift(Dividend, U, Shift_Distance);
      V := Divisor;
      Left_Shift(V, Shift_Distance);

      -- D2 (Initialize J)
      J := M;

      loop
         -- D3 (Calculate Q_Hat)
         D3;

         -- D4 (Multiply and Subtract)
         D4;

         -- D5 (Test Remainder)
         D5;

         -- D7 (Loop on J)
         exit when J = 1;
         J := J - 1;
      end loop;

      -- D8 (Unnormalize)
      for Divisor_Index in Digit_Index_Type range 1 .. N loop
         Remainder.Long_Digits(Divisor_Index) := U.Long_Digits(Divisor_Index);
      end loop;
      Right_Shift(Remainder, Shift_Distance);
   end Divide;


   --
   -- Field F_p Arthemtic Operators
   --

   function Add_Fp(L, R : Very_Long; P : Very_Long) return Very_Long is
      Result : Very_Long(L.Octet_Length);
      Carry  : ACO.Double_Octet;
   begin
      ModAdd_And_Carry(L, R, Result, Carry);
      if Carry = 1 or else (Result >= P) then
         Result := ModSubtract(Result, P);
      end if;
      return Result;
   end Add_Fp;


   function Subtract_Fp(L, R : Very_Long; P : Very_Long) return Very_Long is
      Result : Very_Long(L.Octet_Length);
      Borrow : ACO.Double_Octet;
   begin
      ModSubtract_And_Borrow(L, R, Result, Borrow);
      if Borrow = 1 then
         Result := ModAdd(Result, P);
      end if;
      return Result;
   end Subtract_Fp;


   --
   -- Bit Access
   --

   function Get_Bit(Number : in Very_Long; Bit_Number : in Bit_Index_Type) return Bit is
      Digit_Number : Digit_Index_Type;
      Bit_Position : Bit_Index_Type;
      Mask         : ACO.Octet;
      Digit        : ACO.Octet;
      Result       : Bit;
   begin
      Digit_Number := Digit_Index_Type(1 + Bit_Number / Digit_Bits);
      Bit_Position := Bit_Number mod Digit_Bits;
      Mask         := Octet_Operations.Shift_Left(1, Natural(Bit_Position));
      Digit        := Number.Long_Digits(Digit_Number);

      if (Digit and Mask) /= 0 then
         Result := 1;
      else
         Result := 0;
      end if;
      return Result;
   end Get_Bit;


   procedure Put_Bit(Number : in out Very_Long; Bit_Number : in Bit_Index_Type; Bit_Value  : in Bit) is
      Digit_Number : Digit_Index_Type;
      Bit_Position : Bit_Index_Type;
      Digit        : ACO.Octet;
   begin
      Digit_Number := Digit_Index_Type(1 + Bit_Number / Digit_Bits);
      Bit_Position := Bit_Number mod Digit_Bits;
      Digit        := Number.Long_Digits(Digit_Number);

      if Bit_Value = 1 then
         Digit := Digit or Octet_Operations.Shift_Left(1, Natural(Bit_Position));
      else
         Digit := Digit and not Octet_Operations.Shift_Left(1, Natural(Bit_Position));
      end if;
      Number.Long_Digits(Digit_Number) := Digit;
   end Put_Bit;

end ACO.Math.Very_Longs;
