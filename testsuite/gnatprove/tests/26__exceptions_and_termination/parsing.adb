with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;
procedure Parsing with SPARK_Mode => On is

   --  Ghost specification programs to read a number from a string

   function Read_Digit (C : Character) return Big_Natural is
      (if C in '0' .. '9'
       then To_Big_Integer (Character'Pos (C) - Character'Pos ('0'))
       else 0)
   with Ghost;

   function Read_Number (S : String; Last : Integer) return Big_Natural is
      (if Last < S'First then 0
       else Read_Number (S, Last - 1) * 10 + Read_Digit (S (Last)))
   with Ghost,
     Pre  => Last <= S'Last,
     Post => (for all I in S'Range =>
                (if I < Last then Read_Number (S, I) <= Read_Number'Result)),
     Subprogram_Variant => (Decreases => Last);

   function Read_Number (S : String) return Big_Natural is
      (Read_Number (S, S'Last))
   with Ghost,
     Post => (for all I in S'Range =>
                Read_Number (S, I) <= Read_Number'Result);

   Empty_Input    : exception;
   Unexpected_Char: exception;
   Overflow       : exception;

   --  The procedure parsing a natural number

   procedure Parse_Natural (S : String; Res : out Natural) with
     Post => S'Length > 0
     and then (for all I in S'Range => S (I) in '0' .. '9')
     and then To_Big_Integer (Res) = Read_Number (S),
     Exceptional_Cases =>
       (Empty_Input     => S'Length = 0,
        Unexpected_Char =>
          (for some I in S'Range => S (I) not in '0' .. '9'),
        Overflow        =>
          Read_Number (S) > To_Big_Integer (Integer'Last));

   procedure Parse_Natural (S : String; Res : out Natural) is
   begin
      if S'Length = 0 then
         raise Empty_Input;
      end if;
      Res := 0;

      for I in S'Range loop
         if S (I) not in '0' .. '9' then
            raise Unexpected_Char;
         elsif Res > Integer'Last / 10
           or else Res * 10 > Integer'Last -
             (Character'Pos (S (I)) - Character'Pos ('0'))
         then
            pragma Assert
              (Read_Number (S, I) > To_Big_Integer (Integer'Last));
            raise Overflow;
         end if;

         Res := Res * 10 + (Character'Pos (S (I)) - Character'Pos ('0'));
         pragma Loop_Invariant
           (for all K in S'First .. I => S (K) in '0' .. '9');
         pragma Loop_Invariant
           (Read_Number (S, I) = To_Big_Integer (Res));
      end loop;
   end Parse_Natural;

   function Valid_Natural (S : String) return Boolean is
     (S'Length > 0
      and then (for all I in S'Range => S (I) in '0' .. '9')
      and then Read_Number (S) <= To_Big_Integer (Natural'Last))
   with Ghost;

   type Natural_Option (Present : Boolean := False) is record
      case Present is
         when True  =>
            Val : Natural;
         when False =>
            null;
      end case;
   end record;

   function To_Natural (S : String) return Natural_Option with
     Post =>
       Valid_Natural (S) = To_Natural'Result.Present
       and then
         (if Valid_Natural (S)
          then To_Big_Integer (To_Natural'Result.Val) = Read_Number (S));

   function To_Natural (S : String) return Natural_Option is
   begin
      return Res : Natural_Option (True) do
         Parse_Natural (S, Res.Val);
      end return;
   exception
      when others =>
         return (Present => False);
   end To_Natural;

   function To_Natural (S : String) return Natural with
     Pre  => Valid_Natural (S),
     Post => To_Big_Integer (To_Natural'Result) = Read_Number (S);

   function To_Natural (S : String) return Natural is
   begin
      return Res : Natural do
         Parse_Natural (S, Res);
      end return;
   end To_Natural;

begin
   null;
end;
