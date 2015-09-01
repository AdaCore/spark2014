with Aida.Characters;

package Aida.Conversion is
   pragma SPARK_Mode;

   function Convert_Character_Digit_To_Integer (Source : in  Character) return Integer with
     Pre  => Aida.Characters.Is_Digit (Source),
     Post => Convert_Character_Digit_To_Integer'Result in 0 .. 9,
     Contract_Cases => (Source = '0' => Convert_Character_Digit_To_Integer'Result = 0,
                        Source = '1' => Convert_Character_Digit_To_Integer'Result = 1,
                        Source = '2' => Convert_Character_Digit_To_Integer'Result = 2,
                        Source = '3' => Convert_Character_Digit_To_Integer'Result = 3,
                        Source = '4' => Convert_Character_Digit_To_Integer'Result = 4,
                        Source = '5' => Convert_Character_Digit_To_Integer'Result = 5,
                        Source = '6' => Convert_Character_Digit_To_Integer'Result = 6,
                        Source = '7' => Convert_Character_Digit_To_Integer'Result = 7,
                        Source = '8' => Convert_Character_Digit_To_Integer'Result = 8,
                        Source = '9' => Convert_Character_Digit_To_Integer'Result = 9);

   -- Perhaps one would like to have a function with an Has_Failed flag like the following:
   -- function Convert_Character_Digit_To_Integer (Source     : in  Character;
   --                                              Has_Failed : out Boolean) return Integer;
   -- However, the precondition of
   -- function Convert_Character_Digit_To_Integer (Source : in  Character) return Integer
   -- is trivial enough that such a function should not be nesessary.

   procedure Convert_Character_Digit_To_Integer (Source     : in  Character;
                                                 Target     : out Integer) with
     Pre  => Aida.Characters.Is_Digit (Source),
     Post => Target in 0 .. 9 and Target = Convert_Character_Digit_To_Integer (Source),
     Contract_Cases => (Source = '0' => Target = 0,
                        Source = '1' => Target = 1,
                        Source = '2' => Target = 2,
                        Source = '3' => Target = 3,
                        Source = '4' => Target = 4,
                        Source = '5' => Target = 5,
                        Source = '6' => Target = 6,
                        Source = '7' => Target = 7,
                        Source = '8' => Target = 8,
                        Source = '9' => Target = 9);

   procedure Convert_String_To_Integer (Source     : in  String;
                                        Target     : out Integer;
                                        Has_Failed : out Boolean) with
     Contract_Cases => (Source'Length = 0 => Has_Failed = True,
                        Source'Length = 1 => (if Source(Source'First) = '-' then
                                                Has_Failed = True
                                                  elsif Aida.Characters.Is_Digit (Source (Source'First)) then
                                                (Has_Failed = False and Target = Convert_Character_Digit_To_Integer(Source (Source'First)))
                                                  else
                                                    Has_Failed = True),
                        Source'Length > 1 and Source'Length < 10 => (if (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))) then
                                                                       Has_Failed = False
                                                                         elsif ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Aida.Characters.Is_Digit (Source (Index)))) then
                                                                       Has_Failed = False
                                                                         else
                                                                           Has_Failed = True),
                        Source'Length = 10 => (if (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))) and then
                                                 ((Source(Source'First + 0) = '2' and
                                                    Source(Source'First + 1) = '1' and
                                                    Source(Source'First + 2) = '4' and
                                                    Source(Source'First + 3) = '7' and
                                                    Source(Source'First + 4) = '4' and
                                                    Source(Source'First + 5) = '8' and
                                                    Source(Source'First + 6) = '3' and
                                                    Source(Source'First + 7) = '6' and
                                                    Source(Source'First + 8) = '4' and
                                                    Source(Source'First + 9) <= '7') or
                                                    (Source(Source'First + 0) = '2' and
                                                         Source(Source'First + 1) = '1' and
                                                         Source(Source'First + 2) = '4' and
                                                         Source(Source'First + 3) = '7' and
                                                         Source(Source'First + 4) = '4' and
                                                         Source(Source'First + 5) = '8' and
                                                         Source(Source'First + 6) = '3' and
                                                         Source(Source'First + 7) = '6' and
                                                         Source(Source'First + 8) < '4') or
                                                      (Source(Source'First + 0) = '2' and
                                                             Source(Source'First + 1) = '1' and
                                                             Source(Source'First + 2) = '4' and
                                                             Source(Source'First + 3) = '7' and
                                                             Source(Source'First + 4) = '4' and
                                                             Source(Source'First + 5) = '8' and
                                                             Source(Source'First + 6) = '3' and
                                                             Source(Source'First + 7) < '6') or
                                                    (Source(Source'First + 0) = '2' and
                                                         Source(Source'First + 1) = '1' and
                                                         Source(Source'First + 2) = '4' and
                                                         Source(Source'First + 3) = '7' and
                                                         Source(Source'First + 4) = '4' and
                                                         Source(Source'First + 5) = '8' and
                                                         Source(Source'First + 6) < '3') or
                                                      (Source(Source'First + 0) = '2' and
                                                             Source(Source'First + 1) = '1' and
                                                             Source(Source'First + 2) = '4' and
                                                             Source(Source'First + 3) = '7' and
                                                             Source(Source'First + 4) = '4' and
                                                             Source(Source'First + 5) < '8') or
                                                      (Source(Source'First + 0) = '2' and
                                                             Source(Source'First + 1) = '1' and
                                                             Source(Source'First + 2) = '4' and
                                                             Source(Source'First + 3) = '7' and
                                                             Source(Source'First + 4) < '4') or
                                                      (Source(Source'First + 0) = '2' and
                                                             Source(Source'First + 1) = '1' and
                                                             Source(Source'First + 2) = '4' and
                                                             Source(Source'First + 3) < '7') or
                                                      (Source(Source'First + 0) = '2' and
                                                             Source(Source'First + 1) = '1' and
                                                             Source(Source'First + 2) < '4') or
                                                      (Source(Source'First + 0) = '2' and
                                                             Source(Source'First + 1) < '1') or
                                                      (Source(Source'First + 0) < '2'))
                                                   then
                                                   Has_Failed = False
                                                     elsif ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Aida.Characters.Is_Digit (Source (Index))))
                                                   then
                                                     Has_Failed = False
                                                     else
                                                       Has_Failed = True),
                        Source'Length = 11 => (if (((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Aida.Characters.Is_Digit (Source (Index)))) and then
                                                   ((Source(Source'First + 1) = '2' and
                                                    Source(Source'First + 2) = '1' and
                                                    Source(Source'First + 3) = '4' and
                                                    Source(Source'First + 4) = '7' and
                                                    Source(Source'First + 5) = '4' and
                                                    Source(Source'First + 6) = '8' and
                                                    Source(Source'First + 7) = '3' and
                                                    Source(Source'First + 8) = '6' and
                                                    Source(Source'First + 9) = '4' and
                                                    Source(Source'First + 10) <= '8') or
                                                    (Source(Source'First + 1) = '2' and
                                                         Source(Source'First + 2) = '1' and
                                                         Source(Source'First + 3) = '4' and
                                                         Source(Source'First + 4) = '7' and
                                                         Source(Source'First + 5) = '4' and
                                                         Source(Source'First + 6) = '8' and
                                                         Source(Source'First + 7) = '3' and
                                                         Source(Source'First + 8) = '6' and
                                                         Source(Source'First + 9) < '4') or
                                                      (Source(Source'First + 1) = '2' and
                                                             Source(Source'First + 2) = '1' and
                                                             Source(Source'First + 3) = '4' and
                                                             Source(Source'First + 4) = '7' and
                                                             Source(Source'First + 5) = '4' and
                                                             Source(Source'First + 6) = '8' and
                                                             Source(Source'First + 7) = '3' and
                                                             Source(Source'First + 8) < '6') or
                                                    (Source(Source'First + 1) = '2' and
                                                         Source(Source'First + 2) = '1' and
                                                         Source(Source'First + 3) = '4' and
                                                         Source(Source'First + 4) = '7' and
                                                         Source(Source'First + 5) = '4' and
                                                         Source(Source'First + 6) = '8' and
                                                         Source(Source'First + 7) < '3') or
                                                      (Source(Source'First + 1) = '2' and
                                                             Source(Source'First + 2) = '1' and
                                                             Source(Source'First + 3) = '4' and
                                                             Source(Source'First + 4) = '7' and
                                                             Source(Source'First + 5) = '4' and
                                                             Source(Source'First + 6) < '8') or
                                                      (Source(Source'First + 1) = '2' and
                                                             Source(Source'First + 2) = '1' and
                                                             Source(Source'First + 3) = '4' and
                                                             Source(Source'First + 4) = '7' and
                                                             Source(Source'First + 5) < '4') or
                                                      (Source(Source'First + 1) = '2' and
                                                             Source(Source'First + 2) = '1' and
                                                             Source(Source'First + 3) = '4' and
                                                             Source(Source'First + 4) < '7') or
                                                      (Source(Source'First + 1) = '2' and
                                                             Source(Source'First + 2) = '1' and
                                                             Source(Source'First + 3) < '4') or
                                                      (Source(Source'First + 1) = '2' and
                                                             Source(Source'First + 2) < '1') or
                                                      (Source(Source'First + 1) < '2')))
                                                     then
                                                       Has_Failed = False
                                                         else Has_Failed = True),
                        Source'Length >= 12 => Has_Failed = True);

end Aida.Conversion;
