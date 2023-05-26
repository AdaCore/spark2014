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
         -- The number of hex digits left corresponds to the space left in Result.Long_Digits.
         pragma Loop_Invariant
           ((Number'Last - String_Index + 1)/2 = Positive(Index - Result.Long_Digits'First + 1));
         pragma Loop_Invariant(String_Index in Number'Range);
         pragma Loop_Invariant(Index in Result.Long_Digits'Range);

         Get_Hex_Digit(Number(String_Index),     H_Digit, H_Okay);
         Get_Hex_Digit(Number(String_Index + 1), L_Digit, L_Okay);
         if not (H_Okay and L_Okay) then
            Valid := False;
            exit;
         end if;
         pragma Assert(Index in Result.Long_Digits'Range);
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


function Number_Of_Digits (Number : in Very_Long) return Digit_Count_Type
  with
    Refined_Post =>
      (Number_Of_Digits'Result <= Number.Length) and
      (if Number_Of_Digits'Result > 0 then
         Number.Long_Digits (Number_Of_Digits'Result) /= 0) and
      (for all J in (Number_Of_Digits'Result + 1) .. Number.Long_Digits'Last
         => Number.Long_Digits (J) = 0)
is
   Digit_Count : Digit_Count_Type := 0;
begin
   if not Is_Zero (Number) then
      for Index in Number.Long_Digits'Range loop
         if Number.Long_Digits (Index) /= 0 then
            Digit_Count := Index;
         end if;

         pragma Loop_Invariant
           ((if Digit_Count > 0 then
               (Number.Long_Digits (Digit_Count) /= 0 and
                  Digit_Count in 1 .. Index)) and
            (if Index > Digit_Count then
               (for all J in Digit_Count + 1 .. Index =>
                  Number.Long_Digits (J) = 0)));
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


   procedure Divide
     (Dividend  : in  Very_Long;
      Divisor   : in  Very_Long;
      Quotient  : out Very_Long;
      Remainder : out Very_Long) is separate;

end Very_Longs;
