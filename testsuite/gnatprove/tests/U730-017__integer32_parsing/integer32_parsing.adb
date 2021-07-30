package body Integer32_Parsing with SPARK_Mode is

   function Char_To_Int (c : Character) return Integer_32 is
     (case c is
         when '0'    => 0,
         when '1'    => 1,
         when '2'    => 2,
         when '3'    => 3,
         when '4'    => 4,
         when '5'    => 5,
         when '6'    => 6,
         when '7'    => 7,
         when '8'    => 8,
         when '9'    => 9,
         when others => raise Program_Error)
   with Pre => c in '0' .. '9';
   subtype Digit is Integer_32 range 0 .. 9;
   function Int_To_Char (V : Digit) return Character is
     (case V is
         when 0 => '0',
         when 1 => '1',
         when 2 => '2',
         when 3 => '3',
         when 4 => '4',
         when 5 => '5',
         when 6 => '6',
         when 7 => '7',
         when 8 => '8',
         when 9 => '9');

   Last32 : constant string := "2147483647";
   function Is_Less_Than_Max (s: string; Is_Pos: Boolean; First : Positive) return Boolean is
     (s (First) < Last32 (1) or else
        (s (First) = Last32 (1) and then
           (s (First + 1) < Last32 (2) or else
              (s (First + 1) = Last32 (2) and then
                 (s (First + 2) < Last32 (3) or else
                    (s (First + 2) = Last32 (3) and then
                       (s (First + 3) < Last32 (4) or else
                          (s (First + 3) = Last32 (4) and then
                             (s (First + 4) < Last32 (5) or else
                                (s (First + 4) = Last32 (5) and then
                                   (s (First + 5) < Last32 (6) or else
                                      (s (First + 5) = Last32 (6) and then
                                         (s (First + 6) < Last32 (7) or else
                                            (s (First + 6) = Last32 (7) and then
                                               (s (First + 7) < Last32 (8) or else
                                                  (s (First + 7) = Last32 (8) and then
                                                     (s (First + 8) < Last32 (9) or else
                                                        (s (First + 8) = Last32 (9) and then
                                                           s (First + 9) <= (if Is_Pos then Last32 (10) else Character'Succ (Last32 (10)))))))))))))))))))))
   with Ghost,
     Pre => s'Last > 0 and then First >= s'First and then s'Last - First = 9;

   function Valid_Int (s: string) return Boolean is
     (declare
        Is_Pos : constant Boolean := (s'Length = 0 or else s (s'First) /= '-');
        First  : constant Integer := (if Is_Pos then s'First else s'First + 1);
      begin
        (if First > s'Last then False
         else (for all I in First .. s'Last => s (I) in '0' .. '9')));

   function Valid_Int_32 (s: string) return Boolean is
     (declare
        Is_Pos : constant Boolean := (s'Length = 0 or else s (s'First) /= '-');
        FirstZ : constant Integer := (if Is_Pos then s'First else s'First + 1);
        First  : constant Integer :=
          (if FirstZ > s'Last or else s'Last - FirstZ <= 9
           then FirstZ else s'Last - 9);
      begin
        (if FirstZ > s'Last then False
         else
           (for all I in FirstZ .. First - 1 => s (I) = '0')
            and then (for all I in First .. s'Last => s (I) in '0' .. '9')
            and then (s'Last - First < 9
                      or else Is_Less_Than_Max (s, Is_Pos, First))));

   function Is_Integer_32 (s: string; First, Last : Positive; V : Integer_32) return Boolean is
     (Char_To_Int (s (Last)) = abs (V rem 10)
        and then (if Last /= First then Is_Integer_32 (s, First, Last - 1, V / 10)
                  else V in -9 .. 9))
   with Pre => First >= s'First and then First <= Last and then Last <= s'Last
        and then (for all I in First .. Last => s (I) in '0' .. '9'),
        Subprogram_Variant => (Decreases => Last);

   function Is_Integer_32 (s: string; V : Integer_32) return Boolean is
     (declare
        Is_Pos : constant Boolean := s (s'First) /= '-';
        First  : constant Integer := (if Is_Pos then s'First else s'First + 1);
      begin
        (if Is_Pos then V >= 0 else V <= 0)
        and then Is_Integer_32 (s, First, s'Last, V));

   procedure Lemma_Integer_Rep_Unique (s : string; V1, V2 : Integer_32) is
      procedure Lemma_Integer_Rep_Unique (s : string; First, Last : Positive; V1, V2 : Integer_32) with
        Subprogram_Variant => (Decreases => Last),
        Pre => First >= s'First and then First <= Last and then Last <= s'Last
        and then (for all I in First .. Last => s (I) in '0' .. '9')
        and then Is_Integer_32 (s, First, Last, V1)
        and then Is_Integer_32 (s, First, Last, V2)
        and then (if V1 >= 0 then V2 >= 0 else V2 <= 0),
        Post => V1 = V2
      is
      begin
         pragma Assert (V1 rem 10 = V2 rem 10);
         if Last /= First then
            Lemma_Integer_Rep_Unique (s, First, Last - 1, V1 / 10, V2 / 10);
         end if;
      end Lemma_Integer_Rep_Unique;

      Is_Pos : constant Boolean := s (s'First) /= '-';
      First : constant Integer := (if Is_Pos then s'First else s'First + 1);
   begin
      Lemma_Integer_Rep_Unique (s, First, s'Last, V1, V2);
   end Lemma_Integer_Rep_Unique;

   procedure Lemma_Is_Integer_Extensional (s1, s2 : string; V : Integer_32) is
      procedure Lemma_Is_Integer_Extensional (s1, s2 : string; First1, Last1, First2, Last2 : Positive; V : Integer_32) with
        Subprogram_Variant => (Decreases => Last1),
        Pre => First1 >= s1'First and then First1 <= Last1 and then Last1 <= s1'Last
        and then First2 >= s2'First and then First2 <= Last2 and then Last2 <= s2'Last
        and then (for all I in First1 .. Last1 => s1 (I) in '0' .. '9')
        and then s1 (First1 .. Last1) = s2 (First2 .. Last2)
        and then Is_Integer_32 (s1, First1, Last1, V),
        Post =>  (for all I in First2 .. Last2 => s2 (I) in '0' .. '9')
        and then Is_Integer_32 (s2, First2, Last2, V)
      is
      begin
         if Last1 /= First1 then
            Lemma_Is_Integer_Extensional (s1, s2, First1, Last1 - 1, First2, Last2 - 1, V / 10);
         end if;
      end Lemma_Is_Integer_Extensional;

      Is_Pos : constant Boolean := s1 (s1'First) /= '-';
      First1 : constant Integer := (if Is_Pos then s1'First else s1'First + 1);
      First2 : constant Integer := (if Is_Pos then s2'First else s2'First + 1);
   begin
      Lemma_Is_Integer_Extensional (s1, s2, First1, s1'Last, First2, s2'Last, V);
   end Lemma_Is_Integer_Extensional;

   procedure Lemma_Is_Valid_Extensional (s1, s2 : string) is
      Is_Pos  : constant Boolean := s1 (s1'First) /= '-';
      FirstZ1 : constant Integer := (if Is_Pos then s1'First else s1'First + 1);
      FirstZ2 : constant Integer := (if Is_Pos then s2'First else s2'First + 1);
      First1  : constant Integer :=
        (if FirstZ1 > s1'Last or else s1'Last - FirstZ1 <= 9
         then FirstZ1 else s1'Last - 9);
      First2  : constant Integer :=
        (if FirstZ2 > s2'Last or else s2'Last - FirstZ2 <= 9
         then FirstZ2 else s2'Last - 9);
   begin
      if FirstZ1 <= s1'Last and then s1'Last - First1 = 9 then
        pragma Assert (Is_Less_Than_Max (s1, Is_Pos, First1));
        pragma Assert (Is_Less_Than_Max (s2, Is_Pos, First2));
      end if;
      pragma Assert (for all I in FirstZ2 .. First2 - 1 => s2 (I) = '0');
      pragma Assert (for all I in First2 .. s2'Last => s2 (I) in '0' .. '9');
   end Lemma_Is_Valid_Extensional;

   Tens : constant array (Positive range 1 .. 10) of Integer_32 :=
     (1, 10, 100, 1_000, 10_000, 100_000, 1_000_000, 10_000_000, 100_000_000, 1_000_000_000)
   with Ghost;

   function Parse_Int_32 (s: string) return Integer_32 is
      Is_Pos : constant Boolean := s (s'First) /= '-';
      FirstZ : constant Integer := (if Is_Pos then s'First else s'First + 1);
      First  : constant Integer :=
        (if FirstZ > s'Last or else s'Last - FirstZ <= 9
         then FirstZ else s'Last - 9);
      res    : Integer_32 := 0;
      procedure Prove_Is_Integer with Ghost is
      begin
        for I in FirstZ .. First - 1 loop
          pragma Loop_Invariant (Is_Integer_32 (s, FirstZ, I, res));
        end loop;
        pragma Assert (if FirstZ /= First then Is_Integer_32 (s, FirstZ, First - 1, res));
      end Prove_Is_Integer;
   begin
      Prove_Is_Integer;

      for I in 1 .. 10 loop
         res := res * 10 + (if Is_Pos then 1 else -1) * Char_To_Int (s (I - 1 + First));
         pragma Assert (if Is_Pos then res >= 0 else res <= 0);
         pragma Assert ((if Is_Pos then 1 else -1) * Char_To_Int (s (I - 1 + First)) = res rem 10);
         pragma Assert (Char_To_Int (s (I - 1 + First)) = abs (res rem 10));
         pragma Assert (Is_Integer_32 (s, FirstZ, I - 1 + First, res));
         if I - 1 + First = s'Last then
            pragma Assert (Is_Integer_32 (s, FirstZ, s'Last, res));
            exit;
         end if;
         pragma Assert (if s'Last - First = 9 then res in -(Integer_32'Last / Tens (10 - I)) .. Integer_32'Last / Tens (10 - I));
         pragma Assert (res in -Tens (I + 1) + 1 .. Tens (I + 1) - 1);
      end loop;
      return res;
   end Parse_Int_32;

   procedure Parse_Int_32 (s: string; V : out Integer_32; error : out Boolean) is
      Is_Pos : constant Boolean := s'Length = 0 or else s (s'First) /= '-';
      FirstZ : constant Integer := (if Is_Pos then s'First else s'First + 1);
      First  : Integer;
   begin
      V := 0;
      error := True;
      if FirstZ > s'Last then
         return;
      end if;

      First :=
        (if FirstZ > s'Last or else s'Last - FirstZ <= 9
         then FirstZ else s'Last - 9);

      for I in FirstZ .. First - 1 loop
         if s (I) /= '0' then
           return;
         end if;
         pragma Loop_Invariant (for all k in FirstZ .. I => s (k) = '0');
         pragma Loop_Invariant (Is_Integer_32 (s, FirstZ, I, V));
      end loop;
      pragma Assert (if FirstZ /= First then Is_Integer_32 (s, FirstZ, First - 1, V));

      for I in 1 .. 10 loop
         if s (I - 1 + First) not in '0' .. '9' then
            return;
         end if;
         if I = 10 and then
            (abs (V) > Integer_32'Last / 10
             or else (abs (V) = Integer_32'Last / 10 and then s (I - 1 + First) > (if Is_Pos then '7' else '8')))
         then
            pragma Assert (not Valid_Int_32 (s));
            return;
         end if;
         V := V * 10 + (if Is_Pos then 1 else -1) * Char_To_Int (s (I - 1 + First));
         pragma Assert (if Is_Pos then V >= 0 else V <= 0);
         pragma Assert ((if Is_Pos then 1 else -1) * Char_To_Int (s (I - 1 + First)) = V rem 10);
         pragma Assert (Char_To_Int (s (I - 1 + First)) = abs (V rem 10));
         pragma Assert (Is_Integer_32 (s, FirstZ, I - 1 + First, V));
         if I - 1 + First = s'Last then
            pragma Assert (Valid_Int_32 (s));
            pragma Assert (Is_Integer_32 (s, FirstZ, s'Last, V));
            error := False;
            return;
         end if;
         pragma Assert (V in -Tens (I + 1) + 1 .. Tens (I + 1) - 1);
      end loop;
   end Parse_Int_32;

   function Print_Int_32 (V: Integer_32) return string is
      res : string (1 .. 11) := (others => '0');
      X   : Integer_32 := V;
      top : Natural := 11;
      First : Natural with Ghost;
      procedure Prove_Is_Integer with Ghost is
      begin
        for I in 1 .. 11 loop
          if I >= First then
            pragma Assert (Char_To_Int (res (I)) = abs (V / Tens (12 - I) rem 10));
            pragma Assert (Is_Integer_32 (res, First, I, V / Tens (12 - I)));
          end if;
        end loop;
        pragma Assert (Is_Integer_32 (res, First, 11, V));
      end Prove_Is_Integer;
   begin
      if V = 0 then
         return "0";
      end if;

      for I in 1 .. 10 loop
         res (top) := Int_To_Char (abs (X rem 10));
         top := top - 1;
         X := X / 10;
         exit when X = 0;
         pragma Assert (top = 11 - I);
         pragma Assert (X in -(Integer_32'Last / Tens (I)) .. Integer_32'Last / Tens (I));
         pragma Assert (X = V / Tens (I) / 10);
         pragma Assert (X = V / Tens (I + 1));
         pragma Assert (Char_To_Int (res (12 - I)) = abs (V / Tens (I) rem 10));
         pragma Assert (if V / Tens (I + 1) = Integer_32'Last / Tens (I) then res (12 - I) <= Last32 (11 - I));
         pragma Assert (if V / Tens (I + 1) = -(Integer_32'Last / Tens (I))
                        then res (12 - I) <= Last32 (11 - I)
                          or (I = 1 and res (12 - I) = Character'Succ (Last32 (11 - I))));
      end loop;
      First := top + 1;

      if V < 0 then
        res (top) := '-';
        top := top - 1;
      end if;

      pragma Assert (1 < First or else Is_Less_Than_Max (res, V >= 0, First));

      Prove_Is_Integer;

      declare
        last : constant Integer := 11 - top;
        res0 : constant string (1 .. last) := res (top + 1 .. 11);
      begin
        Lemma_Is_Valid_Extensional (res (top + 1 .. 11), res0);
        Lemma_Is_Integer_Extensional (res (top + 1 .. 11), res0, V);
        return res0;
      end;
   end Print_Int_32;

end Integer32_Parsing;
