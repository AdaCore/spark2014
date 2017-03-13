package Aida is
   pragma SPARK_Mode;

   -- max  2147483647
   -- min -2147483648
   type Int32_T is range -2**31 .. (2**31 - 1);
   for Int32_T'Size use 32;

   type Int64_T is range -2**63 .. (2**63 - 1);
   for Int64_T'Size use 64;

   subtype Nat32_T is Int32_T range 0 .. Int32_T'Last;

   subtype Pos32_T is Int32_T range 1 .. Int32_T'Last;

   type String_T is new Standard.String;

   subtype Character_T is Standard.Character;
   -- This type is a subtype to simplify the Ada code when used together with
   -- String_T instances.

   type Code_Point_T is mod 2**32;
   subtype UTF8_Code_Point_T is Code_Point_T range 0..16#10FFFF#;

   type Hash32_T is mod 2**32;
   for Hash32_T'Size use 32;

   package Character is

      subtype T is Character_T;

      function Is_Digit (Char : T) return Boolean;
      pragma Contract_Cases ((Char = '0' => Is_Digit'Result,
                              Char = '1' => Is_Digit'Result,
                              Char = '2' => Is_Digit'Result,
                              Char = '3' => Is_Digit'Result,
                              Char = '4' => Is_Digit'Result,
                              Char = '5' => Is_Digit'Result,
                              Char = '6' => Is_Digit'Result,
                              Char = '7' => Is_Digit'Result,
                              Char = '8' => Is_Digit'Result,
                              Char = '9' => Is_Digit'Result,
                              Char > '9' => Is_Digit'Result = False,
                              Char < '0' => Is_Digit'Result = False));

      function To_Int32 (Source : in T) return Int32_T;
      pragma Precondition (Is_Digit (Source));
      pragma Postcondition (To_Int32'Result in 0 .. 9);
      pragma Contract_Cases ((Source = '0' => To_Int32'Result = 0,
                              Source = '1' => To_Int32'Result = 1,
                              Source = '2' => To_Int32'Result = 2,
                              Source = '3' => To_Int32'Result = 3,
                              Source = '4' => To_Int32'Result = 4,
                              Source = '5' => To_Int32'Result = 5,
                              Source = '6' => To_Int32'Result = 6,
                              Source = '7' => To_Int32'Result = 7,
                              Source = '8' => To_Int32'Result = 8,
                              Source = '9' => To_Int32'Result = 9));

      procedure To_Int32 (Source : in  T;
                          Target : out Int32_T);
      pragma Precondition (Is_Digit (Source));
      pragma Postcondition (Target in 0 .. 9 and Target = To_Int32 (Source));
      pragma Contract_Cases ((Source = '0' => Target = 0,
                              Source = '1' => Target = 1,
                              Source = '2' => Target = 2,
                              Source = '3' => Target = 3,
                              Source = '4' => Target = 4,
                              Source = '5' => Target = 5,
                              Source = '6' => Target = 6,
                              Source = '7' => Target = 7,
                              Source = '8' => Target = 8,
                              Source = '9' => Target = 9));

   end Character;

   package String is

      subtype T is String_T;

      function I (Source : T;
                  Index  : Natural) return Int32_T;
      pragma Precondition (Index < Source'Length and then Source'First + Index <= Source'Last and then Character.Is_Digit (Source (Source'First + Index)));
      pragma Postcondition (I'Result = Character.To_Int32 (Source (Source'First + Index)));

      procedure To_Int32 (Source     : in  T;
                          Target     : out Int32_T;
                          Has_Failed : out Boolean);
      pragma Global (null);
      pragma Contract_Cases ((Source'Length = 0 => Has_Failed,
                              Source'Length = 1 => (if Source(Source'First) = '-' then
                                                       Has_Failed
                                                    elsif Character.Is_Digit (Source (Source'First)) then
                                                      (Has_Failed = False and Target = I (Source, 0))
                                                    else
                                                       Has_Failed),
                              Source'Length = 2 => (if (for all Index in Source'Range => Character.Is_Digit (Source (Index))) then
                                                      (Has_Failed = False and
                                                         Target = 10*I (Source, 0) + I (Source, 1))
                                                    elsif ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))) then
                                                      (Has_Failed = False and Target = -I (Source, 1))
                                                    else
                                                       Has_Failed),
                              Source'Length = 3 => (if (for all Index in Source'Range => Character.Is_Digit (Source (Index))) then
                                                      (Has_Failed = False and
                                                         Target = 100*I (Source, 0) + 10*I (Source, 1) + I (Source, 2))
                                                    elsif ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))) then
                                                      (Has_Failed = False and Target = -10*I (Source, 1) - I (Source, 2))
                                                    else
                                                       Has_Failed),
                              Source'Length = 4 => (if (for all Index in Source'Range => Character.Is_Digit (Source (Index))) then
                                                      (Has_Failed = False and
                                                         Target = 1_000*I (Source, 0) + 100*I (Source, 1) + 10*I (Source, 2) + I (Source, 3))
                                                    elsif ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))) then
                                                      (Has_Failed = False and Target = -100*I (Source, 1) - 10*I (Source, 2) - I (Source, 3))
                                                    else
                                                       Has_Failed),
                              Source'Length = 5 => (if (for all Index in Source'Range => Character.Is_Digit (Source (Index))) then
                                                      (Has_Failed = False and
                                                         Target = 10_000*I (Source, 0) + 1_000*I (Source, 1) + 100*I (Source, 2) + 10*I (Source, 3) + I (Source, 4))
                                                    elsif ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))) then
                                                      (Has_Failed = False and Target = -1_000*I (Source, 1) - 100*I (Source, 2) - 10*I (Source, 3) - I (Source, 4))
                                                    else
                                                       Has_Failed),
                              Source'Length = 6 => (if (for all Index in Source'Range => Character.Is_Digit (Source (Index))) then
                                                      (Has_Failed = False and
                                                         Target = 100_000*I (Source, 0) + 10_000*I (Source, 1) + 1_000*I (Source, 2) + 100*I (Source, 3) + 10*I (Source, 4) + I (Source, 5))
                                                    elsif ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))) then
                                                      (Has_Failed = False and Target = -10_000*I (Source, 1) - 1_000*I (Source, 2) - 100*I (Source, 3) - 10*I (Source, 4) - I (Source, 5))
                                                    else
                                                       Has_Failed),
                              Source'Length = 7 => (if (for all Index in Source'Range => Character.Is_Digit (Source (Index))) then
                                                      (Has_Failed = False and
                                                         Target = 1_000_000*I (Source, 0) + 100_000*I (Source, 1) + 10_000*I (Source, 2) + 1_000*I (Source, 3) + 100*I (Source, 4) + 10*I (Source, 5) + I (Source, 6))
                                                    elsif ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))) then
                                                      (Has_Failed = False and Target = -100_000*I (Source, 1) - 10_000*I (Source, 2) - 1_000*I (Source, 3) - 100*I (Source, 4) - 10*I (Source, 5) - I (Source, 6))
                                                    else
                                                       Has_Failed),
                              Source'Length = 8 => (if (for all Index in Source'Range => Character.Is_Digit (Source (Index))) then
                                                      (Has_Failed = False and
                                                         Target = 10_000_000*I (Source, 0) + 1_000_000*I (Source, 1) + 100_000*I (Source, 2) + 10_000*I (Source, 3) + 1_000*I (Source, 4) + 100*I (Source, 5) + 10*I (Source, 6) + I (Source, 7))
                                                    elsif ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))) then
                                                      (Has_Failed = False and Target = -1_000_000*I (Source, 1) - 100_000*I (Source, 2) - 10_000*I (Source, 3) - 1_000*I (Source, 4) - 100*I (Source, 5) - 10*I (Source, 6) - I (Source, 7))
                                                    else
                                                       Has_Failed),
                              Source'Length = 9 => (if (for all Index in Source'Range => Character.Is_Digit (Source (Index))) then
                                                      (Has_Failed = False and
                                                         Target = 100_000_000*I (Source, 0) + 10_000_000*I (Source, 1) + 1_000_000*I (Source, 2) + 100_000*I (Source, 3) + 10_000*I (Source, 4) + 1_000*I (Source, 5) + 100*I (Source, 6) + 10*I (Source, 7) + I (Source, 8))
                                                    elsif ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))) then
                                                      (Has_Failed = False and Target = -10_000_000*I (Source, 1) - 1_000_000*I (Source, 2) - 100_000*I (Source, 3) - 10_000*I (Source, 4) - 1_000*I (Source, 5) - 100*I (Source, 6) - 10*I (Source, 7) - I (Source, 8))
                                                    else
                                                       Has_Failed),
                              Source'Length = 10 => (if (for all Index in Source'Range => Character.Is_Digit (Source (Index))) then
                                                       (if (Source(Source'First + 0) = '2' and
                                                          Source(Source'First + 1) = '1' and
                                                          Source(Source'First + 2) = '4' and
                                                          Source(Source'First + 3) = '7' and
                                                          Source(Source'First + 4) = '4' and
                                                          Source(Source'First + 5) = '8' and
                                                          Source(Source'First + 6) = '3' and
                                                          Source(Source'First + 7) = '6' and
                                                          Source(Source'First + 8) = '4' and
                                                          Source(Source'First + 9) < '8') then
                                                          (Has_Failed = False and
                                                               Target = 2_147_483_640 + I (Source, 9))
                                                        elsif (Source(Source'First + 0) = '2' and
                                                            Source(Source'First + 1) = '1' and
                                                            Source(Source'First + 2) = '4' and
                                                            Source(Source'First + 3) = '7' and
                                                            Source(Source'First + 4) = '4' and
                                                            Source(Source'First + 5) = '8' and
                                                            Source(Source'First + 6) = '3' and
                                                            Source(Source'First + 7) = '6' and
                                                            Source(Source'First + 8) < '4') then
                                                          (Has_Failed = False and
                                                               Target = 2_147_483_600 + 10*I (Source, 8) + I (Source, 9))
                                                        elsif (Source(Source'First + 0) = '2' and
                                                            Source(Source'First + 1) = '1' and
                                                            Source(Source'First + 2) = '4' and
                                                            Source(Source'First + 3) = '7' and
                                                            Source(Source'First + 4) = '4' and
                                                            Source(Source'First + 5) = '8' and
                                                            Source(Source'First + 6) = '3' and
                                                            Source(Source'First + 7) < '6') then
                                                          (Has_Failed = False and
                                                               Target = 2_147_483_000 + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9))
                                                        elsif (Source(Source'First + 0) = '2' and
                                                            Source(Source'First + 1) = '1' and
                                                            Source(Source'First + 2) = '4' and
                                                            Source(Source'First + 3) = '7' and
                                                            Source(Source'First + 4) = '4' and
                                                            Source(Source'First + 5) = '8' and
                                                            Source(Source'First + 6) < '3') then
                                                          (Has_Failed = False and
                                                               Target = 2_147_480_000 + 1_000*I (Source, 6) + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9))
                                                        elsif (Source(Source'First + 0) = '2' and
                                                            Source(Source'First + 1) = '1' and
                                                            Source(Source'First + 2) = '4' and
                                                            Source(Source'First + 3) = '7' and
                                                            Source(Source'First + 4) = '4' and
                                                            Source(Source'First + 5) < '8') then
                                                          (Has_Failed = False and
                                                               Target = 2_147_400_000 + 10_000*I (Source, 5) + 1_000*I (Source, 6) + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9))
                                                        elsif (Source(Source'First + 0) = '2' and
                                                            Source(Source'First + 1) = '1' and
                                                            Source(Source'First + 2) = '4' and
                                                            Source(Source'First + 3) = '7' and
                                                            Source(Source'First + 4) < '4') then
                                                          (Has_Failed = False and
                                                               Target = 2_147_000_000 + 100_000*I (Source, 4) + 10_000*I (Source, 5) + 1_000*I (Source, 6) + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9))
                                                        elsif (Source(Source'First + 0) = '2' and
                                                            Source(Source'First + 1) = '1' and
                                                            Source(Source'First + 2) = '4' and
                                                            Source(Source'First + 3) < '7') then
                                                          (Has_Failed = False and
                                                               Target = 2_140_000_000 + 1_000_000*I (Source, 3) + 100_000*I (Source, 4) + 10_000*I (Source, 5) + 1_000*I (Source, 6) + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9))
                                                        elsif (Source(Source'First + 0) = '2' and
                                                            Source(Source'First + 1) = '1' and
                                                            Source(Source'First + 2) < '4') then
                                                          (Has_Failed = False and
                                                               Target = 2_100_000_000 + 10_000_000*I (Source, 2) + 1_000_000*I (Source, 3) + 100_000*I (Source, 4) + 10_000*I (Source, 5) + 1_000*I (Source, 6) + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9))
                                                        elsif (Source(Source'First + 0) = '2' and
                                                            Source(Source'First + 1) < '1') then
                                                          (Has_Failed = False and
                                                               Target = 2_000_000_000 + 10_000_000*I (Source, 2) + 1_000_000*I (Source, 3) + 100_000*I (Source, 4) + 10_000*I (Source, 5) + 1_000*I (Source, 6) + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9))
                                                        elsif (Source(Source'First + 0) < '2') then
                                                          (Has_Failed = False and
                                                               Target = 1_000_000_000*I (Source, 0) + 100_000_000*I (Source, 1) + 10_000_000*I (Source, 2) + 1_000_000*I (Source, 3) + 100_000*I (Source, 4) + 10_000*I (Source, 5) + 1_000*I (Source, 6) + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9))
                                                        else
                                                           Has_Failed)
                                                     elsif ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))) then
                                                       (Has_Failed = False and
                                                          Target = -100_000_000*I (Source, 1) - 10_000_000*I (Source, 2) - 1_000_000*I (Source, 3) - 100_000*I (Source, 4) - 10_000*I (Source, 5) - 1_000*I (Source, 6) - 100*I (Source, 7) - 10*I (Source, 8) - I (Source, 9))
                                                     else
                                                        Has_Failed),
                              Source'Length = 11 => (if ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))) then
                                                       (if (Source(Source'First + 1) = '2' and
                                                          Source(Source'First + 2) = '1' and
                                                          Source(Source'First + 3) = '4' and
                                                          Source(Source'First + 4) = '7' and
                                                          Source(Source'First + 5) = '4' and
                                                          Source(Source'First + 6) = '8' and
                                                          Source(Source'First + 7) = '3' and
                                                          Source(Source'First + 8) = '6' and
                                                          Source(Source'First + 9) = '4' and
                                                          Source(Source'First + 10) <= '8') then
                                                          (Has_Failed = False and
                                                               Target = -2_147_483_640 - I (Source, 10))
                                                        elsif (Source(Source'First + 1) = '2' and
                                                            Source(Source'First + 2) = '1' and
                                                            Source(Source'First + 3) = '4' and
                                                            Source(Source'First + 4) = '7' and
                                                            Source(Source'First + 5) = '4' and
                                                            Source(Source'First + 6) = '8' and
                                                            Source(Source'First + 7) = '3' and
                                                            Source(Source'First + 8) = '6' and
                                                            Source(Source'First + 9) < '4') then
                                                          (Has_Failed = False and
                                                               Target = -2_147_483_600 - 10*I (Source, 9) - I (Source, 10))
                                                        elsif (Source(Source'First + 1) = '2' and
                                                            Source(Source'First + 2) = '1' and
                                                            Source(Source'First + 3) = '4' and
                                                            Source(Source'First + 4) = '7' and
                                                            Source(Source'First + 5) = '4' and
                                                            Source(Source'First + 6) = '8' and
                                                            Source(Source'First + 7) = '3' and
                                                            Source(Source'First + 8) < '6') then
                                                          (Has_Failed = False and
                                                               Target = -2_147_483_000 - 100*I (Source, 8) - 10*I (Source, 9) - I (Source, 10))
                                                        elsif (Source(Source'First + 1) = '2' and
                                                            Source(Source'First + 2) = '1' and
                                                            Source(Source'First + 3) = '4' and
                                                            Source(Source'First + 4) = '7' and
                                                            Source(Source'First + 5) = '4' and
                                                            Source(Source'First + 6) = '8' and
                                                            Source(Source'First + 7) < '3') then
                                                          (Has_Failed = False and
                                                               Target = -2_147_480_000 - 1_000*I (Source, 7) - 100*I (Source, 8) - 10*I (Source, 9) - I (Source, 10))
                                                        elsif
                                                          (Source(Source'First + 1) = '2' and
                                                               Source(Source'First + 2) = '1' and
                                                               Source(Source'First + 3) = '4' and
                                                               Source(Source'First + 4) = '7' and
                                                               Source(Source'First + 5) = '4' and
                                                               Source(Source'First + 6) < '8') then
                                                            (Has_Failed = False and
                                                                 Target = -2_147_400_000 - 10_000*I (Source, 6) - 1_000*I (Source, 7) - 100*I (Source, 8) - 10*I (Source, 9) - I (Source, 10))
                                                        elsif (Source(Source'First + 1) = '2' and
                                                            Source(Source'First + 2) = '1' and
                                                            Source(Source'First + 3) = '4' and
                                                            Source(Source'First + 4) = '7' and
                                                            Source(Source'First + 5) < '4') then
                                                          (Has_Failed = False and
                                                               Target = -2_147_000_000 - 100_000*I (Source, 5) - 10_000*I (Source, 6) - 1_000*I (Source, 7) - 100*I (Source, 8) - 10*I (Source, 9) - I (Source, 10))
                                                        elsif (Source(Source'First + 1) = '2' and
                                                            Source(Source'First + 2) = '1' and
                                                            Source(Source'First + 3) = '4' and
                                                            Source(Source'First + 4) < '7') then
                                                          (Has_Failed = False and
                                                               Target = -2_140_000_000 - 1_000_000*I (Source, 4) - 100_000*I (Source, 5) - 10_000*I (Source, 6) - 1_000*I (Source, 7) - 100*I (Source, 8) - 10*I (Source, 9) - I (Source, 10))
                                                        elsif (Source(Source'First + 1) = '2' and
                                                            Source(Source'First + 2) = '1' and
                                                            Source(Source'First + 3) < '4') then
                                                          (Has_Failed = False and
                                                               Target = -2_100_000_000 - 10_000_000*I (Source, 3) - 1_000_000*I (Source, 4) - 100_000*I (Source, 5) - 10_000*I (Source, 6) - 1_000*I (Source, 7) - 100*I (Source, 8) - 10*I (Source, 9) - I (Source, 10))
                                                        elsif (Source(Source'First + 1) = '2' and
                                                            Source(Source'First + 2) < '1') then
                                                          (Has_Failed = False and
                                                               Target = -2_000_000_000 - 100_000_000*I (Source, 2) - 10_000_000*I (Source, 3) - 1_000_000*I (Source, 4) - 100_000*I (Source, 5) - 10_000*I (Source, 6) - 1_000*I (Source, 7) - 100*I (Source, 8) - 10*I (Source, 9) - I (Source, 10))
                                                        elsif (Source(Source'First + 1) < '2') then
                                                          (Has_Failed = False and
                                                               Target = -1_000_000_000*I (Source, 1) - 100_000_000*I (Source, 2) - 10_000_000*I (Source, 3) - 1_000_000*I (Source, 4) - 100_000*I (Source, 5) - 10_000*I (Source, 6) - 1_000*I (Source, 7) - 100*I (Source, 8) - 10*I (Source, 9) - I (Source, 10))
                                                        else
                                                           Has_Failed)
                                                     else
                                                        Has_Failed),
                              Source'Length >= 12 => Has_Failed));

      function To_Int32 (Source : T) return Int32_T;
      pragma Global (null);
      pragma Precondition ((Source'Length >= 1 and Source'Length <= 11) and then (
                           if Source'Length = 1 then
                              Character.Is_Digit (Source (Source'First))
                           elsif (Source'Length >= 2 and Source'Length <= 9) then
                             ((for all Index in Source'Range => Character.Is_Digit (Source (Index))) or
                                  ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))))
                           elsif Source'Length = 10 then
                             (((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))) or
                                  ((for all Index in Source'Range => Character.Is_Digit (Source (Index))) and then
                                     ((Source(Source'First + 0) = '2' and
                                        Source(Source'First + 1) = '1' and
                                        Source(Source'First + 2) = '4' and
                                        Source(Source'First + 3) = '7' and
                                        Source(Source'First + 4) = '4' and
                                        Source(Source'First + 5) = '8' and
                                        Source(Source'First + 6) = '3' and
                                        Source(Source'First + 7) = '6' and
                                        Source(Source'First + 8) = '4' and
                                        Source(Source'First + 9) < '8') or
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
                                        (Source(Source'First + 0) < '2'))))
                           elsif Source'Length = 11 then
                             (((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))) and then
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
                                       (Source(Source'First + 1) < '2')))));
      pragma Contract_Cases ((Source'Length = 1 => To_Int32'Result = I (Source, 0),
                              Source'Length = 2 => (if (for all Index in Source'Range => Character.Is_Digit (Source (Index))) then
                                                      (To_Int32'Result = 10*I (Source, 0) + I (Source, 1))
                                                    elsif ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))) then
                                                      (To_Int32'Result = -I (Source, 1))),
                              Source'Length = 3 => (if (for all Index in Source'Range => Character.Is_Digit (Source (Index))) then
                                                      (To_Int32'Result = 100*I (Source, 0) + 10*I (Source, 1) + I (Source, 2))
                                                    elsif ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))) then
                                                      (To_Int32'Result = -10*I (Source, 1) - I (Source, 2))),
                              Source'Length = 4 => (if (for all Index in Source'Range => Character.Is_Digit (Source (Index))) then
                                                      (To_Int32'Result = 1_000*I (Source, 0) + 100*I (Source, 1) + 10*I (Source, 2) + I (Source, 3))
                                                    elsif ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))) then
                                                      (To_Int32'Result = -100*I (Source, 1) - 10*I (Source, 2) - I (Source, 3))),
                              Source'Length = 5 => (if (for all Index in Source'Range => Character.Is_Digit (Source (Index))) then
                                                      (To_Int32'Result = 10_000*I (Source, 0) + 1_000*I (Source, 1) + 100*I (Source, 2) + 10*I (Source, 3) + I (Source, 4))
                                                    elsif ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))) then
                                                      (To_Int32'Result = -1_000*I (Source, 1) - 100*I (Source, 2) - 10*I (Source, 3) - I (Source, 4))),
                              Source'Length = 6 => (if (for all Index in Source'Range => Character.Is_Digit (Source (Index))) then
                                                      (To_Int32'Result = 100_000*I (Source, 0) + 10_000*I (Source, 1) + 1_000*I (Source, 2) + 100*I (Source, 3) + 10*I (Source, 4) + I (Source, 5))
                                                    elsif ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))) then
                                                      (To_Int32'Result = -10_000*I (Source, 1) - 1_000*I (Source, 2) - 100*I (Source, 3) - 10*I (Source, 4) - I (Source, 5))),
                              Source'Length = 7 => (if (for all Index in Source'Range => Character.Is_Digit (Source (Index))) then
                                                      (To_Int32'Result = 1_000_000*I (Source, 0) + 100_000*I (Source, 1) + 10_000*I (Source, 2) + 1_000*I (Source, 3) + 100*I (Source, 4) + 10*I (Source, 5) + I (Source, 6))
                                                    elsif ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))) then
                                                      (To_Int32'Result = -100_000*I (Source, 1) - 10_000*I (Source, 2) - 1_000*I (Source, 3) - 100*I (Source, 4) - 10*I (Source, 5) - I (Source, 6))),
                              Source'Length = 8 => (if (for all Index in Source'Range => Character.Is_Digit (Source (Index))) then
                                                      (To_Int32'Result = 10_000_000*I (Source, 0) + 1_000_000*I (Source, 1) + 100_000*I (Source, 2) + 10_000*I (Source, 3) + 1_000*I (Source, 4) + 100*I (Source, 5) + 10*I (Source, 6) + I (Source, 7))
                                                    elsif ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))) then
                                                      (To_Int32'Result = -1_000_000*I (Source, 1) - 100_000*I (Source, 2) - 10_000*I (Source, 3) - 1_000*I (Source, 4) - 100*I (Source, 5) - 10*I (Source, 6) - I (Source, 7))),
                              Source'Length = 9 => (if (for all Index in Source'Range => Character.Is_Digit (Source (Index))) then
                                                      (To_Int32'Result = 100_000_000*I (Source, 0) + 10_000_000*I (Source, 1) + 1_000_000*I (Source, 2) + 100_000*I (Source, 3) + 10_000*I (Source, 4) + 1_000*I (Source, 5) + 100*I (Source, 6) + 10*I (Source, 7) + I (Source, 8))
                                                    elsif ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))) then
                                                      (To_Int32'Result = -10_000_000*I (Source, 1) - 1_000_000*I (Source, 2) - 100_000*I (Source, 3) - 10_000*I (Source, 4) - 1_000*I (Source, 5) - 100*I (Source, 6) - 10*I (Source, 7) - I (Source, 8))),
                              Source'Length = 10 => (if (for all Index in Source'Range => Character.Is_Digit (Source (Index))) then
                                                       (if (Source(Source'First + 0) = '2' and
                                                          Source(Source'First + 1) = '1' and
                                                          Source(Source'First + 2) = '4' and
                                                          Source(Source'First + 3) = '7' and
                                                          Source(Source'First + 4) = '4' and
                                                          Source(Source'First + 5) = '8' and
                                                          Source(Source'First + 6) = '3' and
                                                          Source(Source'First + 7) = '6' and
                                                          Source(Source'First + 8) = '4' and
                                                          Source(Source'First + 9) < '8') then
                                                          (To_Int32'Result = 2_147_483_640 + I (Source, 9))
                                                        elsif (Source(Source'First + 0) = '2' and
                                                            Source(Source'First + 1) = '1' and
                                                            Source(Source'First + 2) = '4' and
                                                            Source(Source'First + 3) = '7' and
                                                            Source(Source'First + 4) = '4' and
                                                            Source(Source'First + 5) = '8' and
                                                            Source(Source'First + 6) = '3' and
                                                            Source(Source'First + 7) = '6' and
                                                            Source(Source'First + 8) < '4') then
                                                          (To_Int32'Result = 2_147_483_600 + 10*I (Source, 8) + I (Source, 9))
                                                        elsif (Source(Source'First + 0) = '2' and
                                                            Source(Source'First + 1) = '1' and
                                                            Source(Source'First + 2) = '4' and
                                                            Source(Source'First + 3) = '7' and
                                                            Source(Source'First + 4) = '4' and
                                                            Source(Source'First + 5) = '8' and
                                                            Source(Source'First + 6) = '3' and
                                                            Source(Source'First + 7) < '6') then
                                                          (To_Int32'Result = 2_147_483_000 + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9))
                                                        elsif (Source(Source'First + 0) = '2' and
                                                            Source(Source'First + 1) = '1' and
                                                            Source(Source'First + 2) = '4' and
                                                            Source(Source'First + 3) = '7' and
                                                            Source(Source'First + 4) = '4' and
                                                            Source(Source'First + 5) = '8' and
                                                            Source(Source'First + 6) < '3') then
                                                          (To_Int32'Result = 2_147_480_000 + 1_000*I (Source, 6) + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9))
                                                        elsif (Source(Source'First + 0) = '2' and
                                                            Source(Source'First + 1) = '1' and
                                                            Source(Source'First + 2) = '4' and
                                                            Source(Source'First + 3) = '7' and
                                                            Source(Source'First + 4) = '4' and
                                                            Source(Source'First + 5) < '8') then
                                                          (To_Int32'Result = 2_147_400_000 + 10_000*I (Source, 5) + 1_000*I (Source, 6) + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9))
                                                        elsif (Source(Source'First + 0) = '2' and
                                                            Source(Source'First + 1) = '1' and
                                                            Source(Source'First + 2) = '4' and
                                                            Source(Source'First + 3) = '7' and
                                                            Source(Source'First + 4) < '4') then
                                                          (To_Int32'Result = 2_147_000_000 + 100_000*I (Source, 4) + 10_000*I (Source, 5) + 1_000*I (Source, 6) + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9))
                                                        elsif (Source(Source'First + 0) = '2' and
                                                            Source(Source'First + 1) = '1' and
                                                            Source(Source'First + 2) = '4' and
                                                            Source(Source'First + 3) < '7') then
                                                          (To_Int32'Result = 2_140_000_000 + 1_000_000*I (Source, 3) + 100_000*I (Source, 4) + 10_000*I (Source, 5) + 1_000*I (Source, 6) + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9))
                                                        elsif (Source(Source'First + 0) = '2' and
                                                            Source(Source'First + 1) = '1' and
                                                            Source(Source'First + 2) < '4') then
                                                          (To_Int32'Result = 2_100_000_000 + 10_000_000*I (Source, 2) + 1_000_000*I (Source, 3) + 100_000*I (Source, 4) + 10_000*I (Source, 5) + 1_000*I (Source, 6) + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9))
                                                        elsif (Source(Source'First + 0) = '2' and
                                                            Source(Source'First + 1) < '1') then
                                                          (To_Int32'Result = 2_000_000_000 + 10_000_000*I (Source, 2) + 1_000_000*I (Source, 3) + 100_000*I (Source, 4) + 10_000*I (Source, 5) + 1_000*I (Source, 6) + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9))
                                                        elsif (Source(Source'First + 0) < '2') then
                                                          (To_Int32'Result = 1_000_000_000*I (Source, 0) + 100_000_000*I (Source, 1) + 10_000_000*I (Source, 2) + 1_000_000*I (Source, 3) + 100_000*I (Source, 4) + 10_000*I (Source, 5) + 1_000*I (Source, 6) + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9)))
                                                     elsif ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))) then
                                                       (To_Int32'Result = -100_000_000*I (Source, 1) - 10_000_000*I (Source, 2) - 1_000_000*I (Source, 3) - 100_000*I (Source, 4) - 10_000*I (Source, 5) - 1_000*I (Source, 6) - 100*I (Source, 7) - 10*I (Source, 8) - I (Source, 9))),
                              Source'Length = 11 => (if ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))) then
                                                       (if (Source(Source'First + 1) = '2' and
                                                          Source(Source'First + 2) = '1' and
                                                          Source(Source'First + 3) = '4' and
                                                          Source(Source'First + 4) = '7' and
                                                          Source(Source'First + 5) = '4' and
                                                          Source(Source'First + 6) = '8' and
                                                          Source(Source'First + 7) = '3' and
                                                          Source(Source'First + 8) = '6' and
                                                          Source(Source'First + 9) = '4' and
                                                          Source(Source'First + 10) <= '8') then
                                                          (To_Int32'Result = -2_147_483_640 - I (Source, 10))
                                                        elsif (Source(Source'First + 1) = '2' and
                                                            Source(Source'First + 2) = '1' and
                                                            Source(Source'First + 3) = '4' and
                                                            Source(Source'First + 4) = '7' and
                                                            Source(Source'First + 5) = '4' and
                                                            Source(Source'First + 6) = '8' and
                                                            Source(Source'First + 7) = '3' and
                                                            Source(Source'First + 8) = '6' and
                                                            Source(Source'First + 9) < '4') then
                                                          (To_Int32'Result = -2_147_483_600 - 10*I (Source, 9) - I (Source, 10))
                                                        elsif (Source(Source'First + 1) = '2' and
                                                            Source(Source'First + 2) = '1' and
                                                            Source(Source'First + 3) = '4' and
                                                            Source(Source'First + 4) = '7' and
                                                            Source(Source'First + 5) = '4' and
                                                            Source(Source'First + 6) = '8' and
                                                            Source(Source'First + 7) = '3' and
                                                            Source(Source'First + 8) < '6') then
                                                          (To_Int32'Result = -2_147_483_000 - 100*I (Source, 8) - 10*I (Source, 9) - I (Source, 10))
                                                        elsif (Source(Source'First + 1) = '2' and
                                                            Source(Source'First + 2) = '1' and
                                                            Source(Source'First + 3) = '4' and
                                                            Source(Source'First + 4) = '7' and
                                                            Source(Source'First + 5) = '4' and
                                                            Source(Source'First + 6) = '8' and
                                                            Source(Source'First + 7) < '3') then
                                                          (To_Int32'Result = -2_147_480_000 - 1_000*I (Source, 7) - 100*I (Source, 8) - 10*I (Source, 9) - I (Source, 10))
                                                        elsif
                                                          (Source(Source'First + 1) = '2' and
                                                               Source(Source'First + 2) = '1' and
                                                               Source(Source'First + 3) = '4' and
                                                               Source(Source'First + 4) = '7' and
                                                               Source(Source'First + 5) = '4' and
                                                               Source(Source'First + 6) < '8') then
                                                            (To_Int32'Result = -2_147_400_000 - 10_000*I (Source, 6) - 1_000*I (Source, 7) - 100*I (Source, 8) - 10*I (Source, 9) - I (Source, 10))
                                                        elsif (Source(Source'First + 1) = '2' and
                                                            Source(Source'First + 2) = '1' and
                                                            Source(Source'First + 3) = '4' and
                                                            Source(Source'First + 4) = '7' and
                                                            Source(Source'First + 5) < '4') then
                                                          (To_Int32'Result = -2_147_000_000 - 100_000*I (Source, 5) - 10_000*I (Source, 6) - 1_000*I (Source, 7) - 100*I (Source, 8) - 10*I (Source, 9) - I (Source, 10))
                                                        elsif (Source(Source'First + 1) = '2' and
                                                            Source(Source'First + 2) = '1' and
                                                            Source(Source'First + 3) = '4' and
                                                            Source(Source'First + 4) < '7') then
                                                          (To_Int32'Result = -2_140_000_000 - 1_000_000*I (Source, 4) - 100_000*I (Source, 5) - 10_000*I (Source, 6) - 1_000*I (Source, 7) - 100*I (Source, 8) - 10*I (Source, 9) - I (Source, 10))
                                                        elsif (Source(Source'First + 1) = '2' and
                                                            Source(Source'First + 2) = '1' and
                                                            Source(Source'First + 3) < '4') then
                                                          (To_Int32'Result = -2_100_000_000 - 10_000_000*I (Source, 3) - 1_000_000*I (Source, 4) - 100_000*I (Source, 5) - 10_000*I (Source, 6) - 1_000*I (Source, 7) - 100*I (Source, 8) - 10*I (Source, 9) - I (Source, 10))
                                                        elsif (Source(Source'First + 1) = '2' and
                                                            Source(Source'First + 2) < '1') then
                                                          (To_Int32'Result = -2_000_000_000 - 100_000_000*I (Source, 2) - 10_000_000*I (Source, 3) - 1_000_000*I (Source, 4) - 100_000*I (Source, 5) - 10_000*I (Source, 6) - 1_000*I (Source, 7) - 100*I (Source, 8) - 10*I (Source, 9) - I (Source, 10))
                                                        elsif (Source(Source'First + 1) < '2') then
                                                          (To_Int32'Result = -1_000_000_000*I (Source, 1) - 100_000_000*I (Source, 2) - 10_000_000*I (Source, 3) - 1_000_000*I (Source, 4) - 100_000*I (Source, 5) - 10_000*I (Source, 6) - 1_000*I (Source, 7) - 100*I (Source, 8) - 10*I (Source, 9) - I (Source, 10))))));

      function Trim (This : T) return T;

      procedure To_Standard_Out (This : T);

      function Hash32 (This : T) return Hash32_T;

   end String;

   package Int32 is

      subtype T is Int32_T;

      function To_String (Value : T) return String_T;

      function To_String (Value : T) return Standard.String;

      procedure To_Standard_Out (This : T);

   end Int32;

   package UTF8_Code_Point is

      package Fs is

         --
         -- General_Category of a code point according to the  Unicode  character
         -- database. The names of the enumeration correspond to the names in the
         -- database.
         --
         type General_Category is
           (  Lu, -- Letter, Uppercase
              Ll, --         Lowercase
              Lt, --         Titlecase
              Lm, --         Modifier
              Lo, --         Other

              Mn, -- Mark, Nonspacing
              Mc, --       Spacing Combining
              Me, --       Enclosing

              Nd, -- Number, Decimal Digit
              Nl, --         Letter
              No, --         Other

              Pc, -- Punctuation, Connector
              Pd, --              Dash
              Ps, --              Open
              Pe, --              Close
              Pi, --              Initial quote
              Pf, --              Final quote
              Po, --              Other

              Sm, -- Symbol, Math
              Sc, --         Currency
              Sk, --         Modifier
              So, --         Other

              Zs, -- Separator, Space
              Zl, --            Line
              Zp, --            Paragraph

              Cc, -- Other, Control
              Cf, --        Format
              Cs, --        Surrogate
              Co, --        Private Use
              Cn  --        Not Assigned
             );
         --
         -- Classes of categories
         --
         subtype Letter      is General_Category range Lu..Lo;
         subtype Mark        is General_Category range Mn..Me;
         subtype Mumber      is General_Category range Nd..No;
         subtype Punctuation is General_Category range Pc..Po;
         subtype Symbol      is General_Category range Sm..So;
         subtype Separator   is General_Category range Zs..Zp;
         subtype Other       is General_Category range Cc..Cn;

      end Fs;

      subtype T is UTF8_Code_Point_T;

      --
      -- Image -- Of an UTF-8 code point
      --
      --    Value - The code point
      --
      -- Returns :
      --
      --    UTF-8 encoded equivalent
      --
      function Image (Value : T) return String_T;

      --
      -- Has_Case -- Case test
      --
      --    Value - Code point
      --
      -- Returns :
      --
      --    True if Value has either an  upper  or  a  lower  case  equivalent
      --    different from Code.
      --
      function Has_Case (Value : T) return Boolean;

      --
      -- Is_Lowercase -- Case test
      --
      --    Value - Code point
      --
      -- Returns :
      --
      --    True if Value is a lower case point
      --
      function Is_Lowercase (Value : T) return Boolean;

      --
      -- Is_Uppercase -- Case test
      --
      --    Value - Code point
      --
      -- Returns :
      --
      --    True if Value is a lower case point
      --
      function Is_Uppercase (Value : T) return Boolean;

      --
      -- To_Lowercase -- Convert to lower case
      --
      --    Value - Code point or UTF-8 encoded string
      --
      -- Returns :
      --
      --    The lower case eqivalent or else Value itself
      --
      function To_Lowercase (Value : T) return T;

      --
      -- To_Uppercase -- Convert to upper case
      --
      --    Value - Code point or UTF-8 encoded string
      --
      -- Returns :
      --
      --    The upper case eqivalent or else Value itself
      --
      function To_Uppercase (Value : T) return T;

      --
      -- Category -- Get category of a code point
      --
      --    Value - Code point
      --
      -- Returns :
      --
      --    The category of value
      --
      function Category (Value : T) return Fs.General_Category;

      --
      -- Is_* -- Category tests
      --
      function Is_Alphanumeric (Value : in T) return Boolean;

      function Is_Digit        (Value : in T) return Boolean;

      function Is_Control      (Value : in T) return Boolean;

      function Is_ISO_646      (Value : in T) return Boolean;

      function Is_Letter       (Value : in T) return Boolean;

      function Is_Lower        (Value : in T) return Boolean;

      function Is_Other_Format (Value : in T) return Boolean;

      function Is_Space        (Value : in T) return Boolean;

      function Is_Title        (Value : in T) return Boolean;

      function Is_Upper        (Value : in T) return Boolean;

      --
      -- Special digits
      --
      function Is_Subscript_Digit (Value : in T) return Boolean;

      function Is_Superscript_Digit (Value : in T) return Boolean;
      --
      -- Ada 2005 identifier sets
      --
      --    identifier_start,  see ARM 2.3(3/2)
      --    identifier_extend, see ARM 2.3(3.1/2)
      --
      function Is_Identifier_Start (Value : in T) return Boolean;

      function Is_Identifier_Extend (Value : in T) return Boolean;

   private
      pragma Inline
        (  Is_Alphanumeric, Is_Control, Is_Digit, Is_ISO_646,
           Is_Letter,       Is_Lower,   Is_Title, Is_Upper,
           Is_Subscript_Digit,  Is_Superscript_Digit,
           Is_Identifier_Start, Is_Identifier_Extend
          );

   end UTF8_Code_Point;

   package UTF8 is

      use Aida.UTF8_Code_Point;

      function Is_Valid_UTF8_Code_Point (Source      : String_T;
                                         Pointer     : Int32_T) return Boolean;

      --
      -- Get -- Get one UTF-8 code point
      --
      --    Source  - The source string
      --    Pointer - The string position to start at
      --    Value   - The result
      --
      -- This  procedure  decodes one UTF-8 code point from the string Source.
      -- It starts at Source (Pointer). After successful completion Pointer is
      -- advanced to the first character following the input.  The  result  is
      -- returned through the parameter Value.
      --
      procedure Get (Source      : String_T;
                     Pointer     : in out Int32_T;
                     Value       : out Aida.UTF8_Code_Point.T);

      --function Is_Valid_UTF8 (Source : String) return Boolean;

      --
      -- Length -- The length of an UTF-8 string
      --
      --    Source - The string containing UTF-8 encoded code points
      --
      -- Returns :
      --
      --    The number of UTF-8 encoded code points in Source
      --
      function Length (Source : String_T) return Nat32_T;

      --
      -- Put -- Put one UTF-8 code point
      --
      --    Destination - The target string
      --    Pointer     - The position where to place the character
      --    Value       - The code point to put
      --
      -- This  procedure  puts  one  UTF-8  code  point into the string Source
      -- starting from the position Source (Pointer). Pointer is then advanced
      -- to the first character following the output.
      --
      procedure Put (Destination : in out String_T;
                     Pointer     : in out Int32_T;
                     Value       : Aida.UTF8_Code_Point.T);

      function To_Lowercase (Value : String_T) return String_T;

      function To_Uppercase (Value : String_T) return String_T;

   end UTF8;

end Aida;
