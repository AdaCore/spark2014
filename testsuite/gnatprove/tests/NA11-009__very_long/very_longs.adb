pragma SPARK_Mode(On);

with Very_Longs.Bit_Operations;

package body Very_Longs is
   use Very_Longs.Bit_Operations;

   Digit_Bits : constant := 8;

   function Shift_Right(Value : Double_Octet; Count : Natural) return Double_Octet
     with
       Import,
       Convention => Intrinsic,
       Global     => null,
       Post       => Shift_Right'Result = Value / (2**Count);


   function Shift_Left(Value : Octet; Count : Natural) return Octet
     with
       Import,
       Convention => Intrinsic,
       Global     => null;


   function Shift_Right(Value : Octet; Count : Natural) return Octet
     with
       Import,
       Convention => Intrinsic,
       Global     => null,
       Post       => Shift_Right'Result = Value / (2**Count);


   procedure Get_Hex_Digit(Raw_Digit : in Character; Digit : out Octet; Valid : out Boolean)
     with Depends => ((Digit, Valid) => Raw_Digit) is
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
   procedure ModAdd_And_Carry
     (L, R : in Very_Long; Result : out Very_Long; Carry : out Double_Octet)
     with
       Depends => (Result =>+ (L, R), Carry => (L, R)),
       Pre  => L.Length = R.Length and L.Length = Result.Length
   is
      L_Digit : Double_Octet;
      R_Digit : Double_Octet;
      Sum     : Double_Octet;
   begin
      Result.Long_Digits := (others => 16#00#);
      Carry := 0;
      for I in L.Long_Digits'Range loop
         L_Digit := Double_Octet(L.Long_Digits(I));
         R_Digit := Double_Octet(R.Long_Digits(I));
         Sum     := L_Digit + R_Digit + Carry;
         Carry   := Shift_Right(Sum, Digit_Bits);
         Result.Long_Digits(I) := TakeLSB_From16(Sum);
      end loop;
   end ModAdd_And_Carry;


   -- Similar to ModSubtract except that final borrow is written to Borrow.
   procedure ModSubtract_And_Borrow
     (L, R : in Very_Long; Result : out Very_Long; Borrow : out Double_Octet)
     with
       Depends => (Result =>+ (L, R), Borrow => (L, R)),
       Pre  => L.Length = R.Length and L.Length = Result.Length
   is
      L_Digit    : Double_Octet;
      R_Digit    : Double_Octet;
      Difference : Double_Octet;
   begin
      Result.Long_Digits := (others => 16#00#);
      Borrow := 0;
      for I in L.Long_Digits'Range loop
         L_Digit    := Double_Octet(L.Long_Digits(I));
         R_Digit    := Double_Octet(R.Long_Digits(I));
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

   function Make_From_Natural
     (Number : in Natural; Length : in Digit_Index_Type) return Very_Long is

      Result : Very_Long(Length);
      Temp   : Natural;
   begin
      pragma Assert(Result.Length = Length);
      Result.Long_Digits := (others => 16#00#);
      Temp := Number;
      for Index in Result.Long_Digits'Range loop
         Result.Long_Digits(Index) := Octet(Temp rem 256);
         Temp := Temp / 256;
      end loop;
      return Result;
   end Make_From_Natural;


   procedure Make_From_Hex_String
     (Number : in String; Result : out Very_Long; Valid : out Boolean) is

      Index        : Digit_Index_Type;
      String_Index : Positive;
      H_Digit      : Octet;
      L_Digit      : Octet;
      H_Okay       : Boolean;
      L_Okay       : Boolean;
   begin  -- Make_From_Hex_String
      Result.Long_Digits := (others => 16#00#);
      Valid := True;

      Index := Result.Long_Digits'Last;
      String_Index := Number'First;
      loop
         pragma Loop_Invariant
           (String_Index = Natural(2*(Result.Long_Digits'Last - Index)) + Number'First);

         Get_Hex_Digit(Number(String_Index),     H_Digit, H_Okay);
         Get_Hex_Digit(Number(String_Index + 1), L_Digit, L_Okay);
         if not (H_Okay and L_Okay) then
            Valid := False;
            exit;
         end if;
         Result.Long_Digits(Index) := 16 * H_Digit + L_Digit;
         exit when Index = Result.Long_Digits'First;
         Index := Index - 1;
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


   function Number_Of_Digits (Number : Very_Long) return Digit_Count_Type
     with
       Refined_Post =>
         (if Number_Of_Digits'Result > 0 then
            Number.Long_Digits(Number_Of_Digits'Result) /= 0) and
         (for all I in (Number_Of_Digits'Result + 1) .. Number.Long_Digits'Last =>
            Number.Long_Digits(I) = 0)
   is
      Digit_Count : Digit_Count_Type := 0;
   begin
      if not Is_Zero (Number) then
         for I in Number.Long_Digits'Range loop
            if Number.Long_Digits (I) /= 0 then
               Digit_Count := I;
            end if;

            pragma Loop_Invariant
              (if I > Digit_Count then
                 (for all J in Digit_Count + 1 .. I => Number.Long_Digits(J) = 0));
         end loop;
      end if;
      return Digit_Count;
   end Number_Of_Digits;


   --
   -- Arithmetic Operators
   --

   function ModAdd(L, R : Very_Long) return Very_Long is
      Result  : Very_Long(L.Length);
      L_Digit : Double_Octet;
      R_Digit : Double_Octet;
      Sum     : Double_Octet;
      Carry   : Double_Octet;
   begin
      Result.Long_Digits := (others => 16#00#);
      Carry := 0;
      for I in L.Long_Digits'Range loop
         L_Digit := Double_Octet(L.Long_Digits(I));
         R_Digit := Double_Octet(R.Long_Digits(I));
         Sum     := L_Digit + R_Digit + Carry;
         Carry   := Shift_Right(Sum, Digit_Bits);
         Result.Long_Digits(I) := TakeLSB_From16(Sum);
      end loop;
      return Result;
   end ModAdd;


   function ModSubtract(L, R : Very_Long) return Very_Long is
      Result     : Very_Long(L.Length);
      L_Digit    : Double_Octet;
      R_Digit    : Double_Octet;
      Difference : Double_Octet;
      Borrow     : Double_Octet;
   begin
      Result.Long_Digits := (others => 16#00#);
      Borrow := 0;
      for I in L.Long_Digits'Range loop
         L_Digit    := Double_Octet(L.Long_Digits(I));
         R_Digit    := Double_Octet(R.Long_Digits(I));
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


   -- This is "Algorithm M" from Knuth's "The Art of Computer Programming, Volume 2: Semi-
   -- numerical Algorithms" (third edition, published by Addison-Wesley, copyright 1998, pages
   -- 268-270).
   --
   function ModMultiply(L, R : Very_Long) return Very_Long is
      Result : Very_Long(L.Length);
      L_Digit : Double_Octet;
      R_Digit : Double_Octet;
      T_Digit : Double_Octet;
      Temp    : Double_Octet;
      Carry   : Double_Octet;
   begin
      -- Prepare Result's digit array.
      Result.Long_Digits := (others => 16#00#);

      -- Do the multiplication.
      for J in R.Long_Digits'Range loop
         Carry := 0;
         for I in L.Long_Digits'Range loop
            L_Digit := Double_Octet(L.Long_Digits(I));
            R_Digit := Double_Octet(R.Long_Digits(J));
            if I + J - 1 in Result.Long_Digits'Range then
               T_Digit := Double_Octet(Result.Long_Digits(I + J - 1));
               Temp    := (L_Digit * R_Digit) + T_Digit + Carry;
               Result.Long_Digits(I + J - 1) := TakeLSB_From16(Temp);
               Carry   := Shift_Right(Temp, Digit_Bits);
            end if;
         end loop;
      end loop;
      return Result;
   end ModMultiply;


   function "*"(L, R : Very_Long) return Very_Long is
      Result  : Very_Long(L.Length + R.Length);
      L_Digit : Double_Octet;
      R_Digit : Double_Octet;
      T_Digit : Double_Octet;
      Temp    : Double_Octet;
      Carry   : Double_Octet;
   begin
      -- Prepare Result's digit array.
      Result.Long_Digits := (others => 16#00#);

      -- Do the multiplication.
      for J in R.Long_Digits'Range loop
         Carry := 0;
         for I in L.Long_Digits'Range loop
            L_Digit  := Double_Octet(L.Long_Digits(I));
            R_Digit  := Double_Octet(R.Long_Digits(J));
            T_Digit  := Double_Octet(Result.Long_Digits(I + J - 1));
            Temp     := (L_Digit * R_Digit) + T_Digit + Carry;
            Result.Long_Digits(I + J - 1) := TakeLSB_From16(Temp);
            Carry    := Shift_Right(Temp, Digit_Bits);
         end loop;
         Result.Long_Digits(L.Length + J) := TakeLSB_From16(Carry);
      end loop;
      return Result;
   end "*";


   -- This is "Algorithm D" from Knuth's "The Art of Computer Programming, Volume 2: Semi-
   -- numerical Algorithms" (third edition, published by Addison-Wesley, copyright 1998, pages
   -- 272-276).
   --
   procedure Divide
     (Dividend  : in  Very_Long;
      Divisor   : in  Very_Long;
      Quotient  : out Very_Long;
      Remainder : out Very_Long) is

      -- Divisor has N digits. This subtype is used for values of N. The divisor must have at
      -- least one digit.
      subtype Divisor_Digits_Count_Type is Digit_Index_Type range 1 .. Divisor.Length;

      -- Dividend has 2*Divisor.Length = M + N digits. This subtype is used for values of M.
      -- Quotient has M + 1 digits.
      subtype Quotient_Digits_Count_Type is
        Digit_Index_Type range Divisor.Length .. 2*Divisor.Length - 1;

      -- This subtype is used for shift distances during the normalization and unnormalization
      -- steps.
      subtype Shift_Type is Natural range 0 .. 7;

      -- Refer to the document on multiprecision division to understand the names here.
      N               : Divisor_Digits_Count_Type;    -- Number of non-zero digits in divisor.
      M               : Quotient_Digits_Count_Type;   -- Number of digits in dividend is m + n.
      Shift_Distance  : Shift_Type;                   -- Number of bits to shift divisor.
      U               : Very_Long(Dividend.Length + 1);  -- Normalized dividend.
      V               : Very_Long(Divisor.Length);       -- Normalized divisor.
      Q_Hat           : Double_Octet;
      Current_Borrow  : Double_Octet;

      -- Returns the left shift distance required to move a 1 bit into the most significant
      -- position of Digit.
      function Get_Shift_Distance(Digit : Octet) return Shift_Type
        with Pre => Digit /= 0
      is
         Mask     : constant Octet := 16#01#;
         Distance : Shift_Type := 0;
      begin
         for I in Shift_Type loop
            if (Digit and Shift_Left(Mask, I)) /= 0 then
               Distance := Shift_Type'Last - I;
            end if;
         end loop;
         return Distance;
      end Get_Shift_Distance;

      -- Shifts Number to the left by Distance bits, putting the result into Result.
      procedure Full_Left_Shift
        (Number : in Very_Long; Result : out Very_Long; Distance : in Shift_Type)
        with
          Depends => (Result =>+ (Number, Distance)),
          Pre => Result.Length = Number.Length + 1
      is
         Old_Overflow  : Octet := 16#00#;
         New_Overflow  : Octet;
         Overflow_Mask : Octet;
      begin
         Result.Long_Digits := (others => 16#00#);
         Overflow_Mask := Shift_Left(16#FF#, 8 - Distance);
         for I in Number.Long_Digits'Range loop
            New_Overflow := Shift_Right(Number.Long_Digits(I) and Overflow_Mask, 8 - Distance);
            Result.Long_Digits(I) := Shift_Left(Number.Long_Digits(I), Distance);
            Result.Long_Digits(I) := Result.Long_Digits(I) or Old_Overflow;
            Old_Overflow := New_Overflow;
         end loop;
         Result.Long_Digits(Result.Long_Digits'Last) := Old_Overflow;
      end Full_Left_Shift;

      -- Shifts Number to the left by Distance bits. The final overflow is dropped (should be
      -- zero when used as below).
      procedure Left_Shift(Number : in out Very_Long; Distance : in Shift_Type)
        with Depends => (Number =>+ Distance)
      is
         Old_Overflow  : Octet := 16#00#;
         New_Overflow  : Octet;
         Overflow_Mask : Octet;
      begin
         Overflow_Mask := Shift_Left(16#FF#, 8 - Distance);
         for I in Number.Long_Digits'Range loop
            New_Overflow := Shift_Right(Number.Long_Digits(I) and Overflow_Mask, 8 - Distance);
            Number.Long_Digits(I) := Shift_Left(Number.Long_Digits(I), Distance);
            Number.Long_Digits(I) := Number.Long_Digits(I) or Old_Overflow;
            Old_Overflow := New_Overflow;
         end loop;
      end Left_Shift;

      -- Shifts Number to the right by Distance bits. The final overflow is dropped (should be
      -- zero (I think) when used as below).
      procedure Right_Shift(Number : in out Very_Long; Distance : in Shift_Type)
        with Depends => (Number =>+ Distance)
      is
         Old_Overflow  : Octet := 16#00#;
         New_Overflow  : Octet;
         Overflow_Mask : Octet;
      begin
         Overflow_Mask := Shift_Right(16#FF#, 8 - Distance);
         for I in reverse Number.Long_Digits'Range loop
            New_Overflow := Number.Long_Digits(I) and Overflow_Mask;
            Number.Long_Digits(I) := Shift_Right(Number.Long_Digits(I), Distance);
            Number.Long_Digits(I) :=
              Number.Long_Digits(I) or Shift_Left(Old_Overflow, 8 - Distance);
            Old_Overflow := New_Overflow;
         end loop;
      end Right_Shift;

      procedure D3(J : in Digit_Index_Type)
        with
          Global => (Input => (N, U, V), Output => Q_Hat),
          Depends => (Q_Hat => (J, N, U, V)),
          Pre => (N > 1 and J + N <= U.Length)
      is
         Temporary_Digit : Double_Octet;
         R_Hat           : Double_Octet;
      begin
         Temporary_Digit :=
           256 * Double_Octet(U.Long_Digits(J + N)) + Double_Octet(U.Long_Digits(J + N - 1));
         Q_Hat := Temporary_Digit / Double_Octet(V.Long_Digits(N));
         -- Q_Hat has at most 9 bits.

         R_Hat := Temporary_Digit mod Double_Octet(V.Long_Digits(N));
         -- R_Hat has at most 8 bits.

         if Q_Hat = 256 or
            (Q_Hat * Double_Octet(V.Long_Digits(N - 1)) >
               256 * R_Hat + Double_Octet(U.Long_Digits((J + N) - 2))) then

            Q_Hat := Q_Hat - 1;
            R_Hat := R_Hat + Double_Octet(V.Long_Digits(N));
         end if;
         if R_Hat < 256 then
            -- This is the same test as above. Should it be moved into a separate subprogram?
            if Q_Hat = 256 or
               (Q_Hat * Double_Octet(V.Long_Digits(N - 1)) >
                  256 * R_Hat + Double_Octet(U.Long_Digits((J + N) - 2))) then

               Q_Hat := Q_Hat - 1;
            end if;
         end if;
         -- At this point Q_Hat should be only an eight bit number.
      end D3;

      procedure D4(J : in Digit_Index_Type)
        with
          Global => (Input => (N, Q_Hat, V), Output => Current_Borrow, In_Out => U),
          Depends => (Current_Borrow => (J, N, Q_Hat, U, V), U => (J, N, Q_Hat, U, V))
      is
         Carry           : Double_Octet;
         Product         : Double_Octet;
         Temporary_Digit : Double_Octet;
         Future_Borrow   : Double_Octet;
      begin
         Carry := 0;
         Current_Borrow := 0;
         for Divisor_Index in Digit_Index_Type range 1 .. N loop
            Product := Q_Hat * Double_Octet(V.Long_Digits(Divisor_Index)) + Carry;
            Carry := Shift_Right(Product, 8);

            Temporary_Digit := Product and 16#00FF#;
            if (Double_Octet(U.Long_Digits(J + Divisor_Index - 1)) >=
                Temporary_Digit + Current_Borrow) then

               Future_Borrow := 0;
            else
               Future_Borrow := 1;
            end if;
            U.Long_Digits(J + Divisor_Index - 1) :=
              Octet(
                ((Double_Octet(U.Long_Digits(J + Divisor_Index - 1)) - Temporary_Digit) - Current_Borrow) and 16#00FF#);
            Current_Borrow := Future_Borrow;
         end loop;

         -- The last digit is handled as a special case.
         if Double_Octet(U.Long_Digits(J + N)) >= Carry + Current_Borrow then
            Future_Borrow := 0;
         else
            Future_Borrow := 1;
         end if;
         U.Long_Digits(J + N) :=
           Octet(
             ((Double_Octet(U.Long_Digits(J + N)) - Carry) - Current_Borrow) and 16#00FF#);
         Current_Borrow := Future_Borrow;
      end D4;

      procedure D5(J : in Digit_Index_Type)
        with
          Global => (Input => (Current_Borrow, N, Q_Hat, V), In_Out => (Quotient, U)),
          Depends =>
            (Quotient => (Current_Borrow, J, Q_Hat, Quotient), U => (Current_Borrow, J, N, U, V))
      is
         Carry : Double_Octet;
         Sum   : Double_Octet;
      begin
         Quotient.Long_Digits(J) := Octet(Q_Hat);  -- This is where Q_Hat must be eight bits!
         if Current_Borrow /= 0 then

            -- D6 (Add Back)
            Quotient.Long_Digits(J) := Quotient.Long_Digits(J) - 1;
            Carry := 0;
            for Divisor_Index in Digit_Index_Type range 1 .. N loop
               Sum := Double_Octet(U.Long_Digits(J + Divisor_Index - 1)) +
                      Double_Octet(V.Long_Digits(Divisor_Index)) + Carry;
               U.Long_Digits(J + Divisor_Index - 1) := TakeLSB_From16(Sum);
               Carry := Shift_Right(Sum, 8);
            end loop;
            U.Long_Digits(J + N) := U.Long_Digits(J + N) + TakeLSB_From16(Carry);
         end if;
      end D5;

   begin  -- Divide
      Quotient.Long_Digits  := (others => 16#00#);
      Remainder.Long_Digits := (others => 16#00#);

      -- D0
      N := Number_Of_Digits(Divisor);
      M := Dividend.Length - N;

      -- D1 (Normalize)
      Shift_Distance := Get_Shift_Distance(Divisor.Long_Digits(N));
      Full_Left_Shift(Dividend, U, Shift_Distance);
      V := Divisor;
      Left_Shift(V, Shift_Distance);

      -- D2 (Initialize J)
      for J in reverse Digit_Index_Type range 1 .. M + 1 loop
         -- D3 (Calculate Q_Hat)
         D3(J);

         -- D4 (Multiply and Subtract)
         D4(J);

         -- D5 (Test Remainder)
         D5(J);

         -- D7 (Loop on J)
      end loop;

      -- D8 (Unnormalize)
      for Divisor_Index in Digit_Index_Type range 1 .. N loop
         Remainder.Long_Digits(Divisor_Index) := U.Long_Digits(Divisor_Index);
      end loop;
      Right_Shift(Remainder, Shift_Distance);
   end Divide;

end Very_Longs;
