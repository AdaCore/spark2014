with ADC;
with DAC;
with Ada.Text_IO;
with Ada.Integer_Text_IO;
with Ada.Numerics.Elementary_Functions; use Ada.Numerics.Elementary_Functions;

procedure Control_Structures is

   subtype Uppercase is Character range 'A' .. 'Z';

   A, B, C       : Integer;
   D, E, F, G, H : Integer;
   Ch            : Character;
   Temperature   : Integer;
   Valve_Setting : Integer;
   Value         : Integer;
   Sum           : Integer;
   Success       : Boolean;
   Approx, X, Y  : Float;
   Tolerance     : constant Float := 0.0001;
   Letter        : Uppercase := 'Q';

   procedure Calculate_Valve (Current_Temp : in  Integer;
                              New_Setting  : out Integer) is
   begin
      New_Setting := 2 * Current_Temp;
   end Calculate_Valve;

   function Double (First  : in Integer;
                    Second : in Integer) return Boolean is
      (abs Second = 2 * abs First);


begin
   A := 1;
   B := 2;
   C := 3;
   D := 3;
   E := 4;
   Ch := 'D';
   X := 123.4546;


   if A < 0 then
      A := -A;
      D := 1;
   end if;

   if A in 1 .. 12 then
      B := 17;
   end if;

   if A > B then
      E := 1;
      F := A;
   else
      E := 2;
      F := B;
   end if;


   if A = B then
      F := 3;
   elsif A > B then
      F := 4;
   else
      F := 5;
   end if;


   if A > B and A > C then
      G := 6;
   elsif B > A and B > C then
      G := 7;
   elsif C > A and C > B then
      G := 8;
   end if;

   Success := True;
   case Ch is
      when 'a' .. 'z' =>
         H := 1;
      when 'A' .. 'Z' =>
         H := 2;
      when '0' .. '9' =>
         H := 3;
      when '.' | '!' | '?' =>
         H := 4;
      when others =>
         H := 5;
         Success := False;
   end case;

   -- If  expressions
   if A > B then
      C := D + 5;
   else
      C := F / 2;
   end if;

   C := (if A > B then D + 5 else F / 2);

   if A > B then
      C := D + 5;
   elsif A = B then
      C := 2 * A;
   else
      C := F / 2;
   end if;

   C := (if A > B then D + 5 elsif A = B then 2 * A else F / 2);

   if X >= 0.0 then
      Y := Sqrt (X);
   else
      Y := Sqrt (-2.0 * X);
   end if;

   Y := Sqrt (if X >= 0.0 then X else -2.0 * X);

  -- Check syntax for Boolean if expression examples

   if (if C - D = 0 then E > 2 else True) then
      null;
   end if;

   if (if C - D = 0 then E > 2) then
      null;
   end if;

   if (if A < 0 then B < 0) then
      null;
   end if;


   -- case expression example
   Value := (case Letter is
                when 'A' | 'E' | 'I' | 'L' | 'U' |
                     'N' | 'O' | 'R' | 'S' | 'T'     => 1,
                when 'D' | 'G'                       => 2,
                when 'B' | 'C' | 'M' | 'P'           => 3,
                when 'F' | 'H' | 'V' | 'W' | 'Y'     => 4,
                when 'K'                             => 5,
                when 'J' | 'X'                       => 8,
                when 'Q' | 'Z'                       => 10);


   -- loop examples

   Sum := 0;
   loop
      Ada.Integer_Text_IO.Get (Value);
      exit when Value < 0;
      Sum := Sum + Value;
   end loop;


   Approx := X / 2.0;
   while abs (X - Approx ** 2) > Tolerance loop
      Approx := 0.5 * (Approx + X / Approx);
   end loop;

   for Count in Integer range 5 .. 8 loop
      Ada.Integer_Text_IO.Put (Count);
   end loop;

   for Count in reverse Integer range 5 .. 8 loop
      Ada.Integer_Text_IO.Put (Count);
   end loop;

   A := 9;
   B := 2;

   for Count in Integer range A .. B loop -- With a null range, this
      Ada.Integer_Text_IO.Put (Count);    -- loop iterates zero times
   end loop;

   for Count in reverse Integer range A .. B loop -- With a null range, this
      Ada.Integer_Text_IO.Put (Count);            -- loop iterates zero times
   end loop;

   loop
      ADC.Read (Temperature);          -- Read the temperature from the ADC
      Calculate_Valve (Current_Temp => Temperature,    -- Calculate the new
                       New_Setting  => Valve_Setting); -- gas valve setting
      DAC.Write (Valve_Setting);       -- Change the gas valve setting
   end loop;


end Control_Structures;
