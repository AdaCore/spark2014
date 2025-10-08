package body Array_Comparison_Str is

   pragma Warnings (Off, "analyzing unreferenced procedure *");
   pragma Warnings (Off, "subprogram * has no effect");

   procedure P_Str (I : Integer) is

      --  Should be the same value that is chosen in the implementation. See
      --  CE_Max_Print_Chars_String in ce_pretty_printing.adb.
      Str_Trunc_Limit : constant := 30;

   begin

      --  Note: In the implementation string literals get treated as having an
      --  implicit 'others' => 'a'. This is not the case for aggregates where
      --  the presence and value of the 'others' is taken to be the same as in
      --  the aggregate.

      case I is

         --------------
         --  GROUP 1 --
         --------------

         when 10 =>
            declare
               --  "Short" string with less than 15 'a' characters.
               X : String := "abacadaea";
            begin
               pragma Assert (X /= X);
            end;

         when 12 =>
            declare
               --  "Short" string with no 'a' characters.
               X : String := "XbXcXdXeX";
            begin
               pragma Assert (X /= X);
            end;

         when 13 =>
            declare
               --  "Short" string with less than 15 'X' characters (explicit
               --  value for 'others').
               X : String (1 .. 9) :=
                 (2 => 'b', 4 => 'c', 6 => 'd', 8 => 'e', others => 'X');
            begin
               pragma Assert (X /= X);
            end;

         --------------
         --  GROUP 2 --
         --------------

         when 21 =>
            declare
               --  "Short" string with more than 15 'a' characters.
               X : String := "baaaaaaaaaaaaaaaaac";
            begin
               pragma Assert (X /= X);
            end;

         when 22 =>
            declare
               --  The same string as above, aggregate notation, no 'others'.
               X : String := (1 => 'b', 2 .. 18 => 'a', 19 => 'c');
            begin
               pragma Assert (X /= X);
            end;

         when 23 =>
            declare
               --  The same string as above, explicit 'others'.
               X : String (1 .. 19) := (1 => 'b', 19 => 'c', others => 'a');
            begin
               pragma Assert (X /= X);
            end;

         --------------
         --  GROUP 3 --
         --------------

         when 31 =>
            declare
               --  "Short" string with more than 15 'a' characters and more
               --  than 5 unique elements, string notation.
               X : String := "baaaaaaaaaaaaaaaaacdeff";
            begin
               pragma Assert (X /= X);
            end;

         when 32 =>
            declare
               --  The same string as above, aggregate notation, no 'others'.
               X : String :=
                 (1        => 'b',
                  2 .. 18  => 'a',
                  19       => 'c',
                  20       => 'd',
                  21       => 'e',
                  22 .. 23 => 'f');
            begin
               pragma Assert (X /= X);
            end;

         when 33 =>
            declare
               --  The same string as above, aggregate notation, with 'others'.
               X : String (1 .. 23) :=
                 (1        => 'b',
                  19       => 'c',
                  20       => 'd',
                  21       => 'e',
                  22 .. 23 => 'f',
                  others   => 'a');
            begin
               pragma Assert (X /= X);
            end;

         --------------
         --  GROUP 4 --
         --------------

         when 41 =>
            declare
               --  "Long" string literal with more than 15 'a' characters.
               X : String :=
                 "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do "
                 & "eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut "
                 & "enim ad minim veniam, quis nostrud exercitation ullamco laboris "
                 & "nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor "
                 & "in reprehenderit in voluptate velit esse cillum dolore eu "
                 & "fugiat nulla pariatur. Excepteur sint occaecat cupidatat non "
                 & "proident, sunt in culpa qui officia deserunt mollit anim id "
                 & "est laborum.";
            begin
               pragma Assert (X /= X);
            end;

         when 42 =>
            declare
               --  The same as above, but no 'a' characters.
               X : String :=
                 "L$rem ipsum dolor sit $met, consectetur $dipiscing elit, sed do "
                 & "eiusmod tempor incididunt ut l$bore et dolore m$gn$ $liqu$. Ut "
                 & "enim $d minim veni$m, quis nostrud exercit$tion ull$mco l$boris "
                 & "nisi ut $liquip ex e$ commodo consequ$t. Duis $ute irure dolor "
                 & "in reprehenderit in volupt$te velit esse cillum dolore eu "
                 & "fugi$t null$ p$ri$tur. Excepteur sint occ$ec$t cupid$t$t non "
                 & "proident, sunt in culp$ qui offici$ deserunt mollit $nim id "
                 & "est l$borum.";
            begin
               pragma Assert (X /= X);
            end;

         when 43 =>
            declare
               --  "Long" string aggregate, no 'others'.
               X : String (1 .. 300) :=
                 (1          => 'b',
                  2 .. 18    => 'a',
                  19         => 'c',
                  20         => 'd',
                  21 .. 298  => 'e',
                  299 .. 300 => 'f');
            begin
               pragma Assert (X /= X);
            end;

         when 44 =>
            declare
               --  The same as above, with 'others'.
               X : String (1 .. 300) :=
                 (1          => 'b',
                  19         => 'c',
                  20         => 'd',
                  21 .. 298  => 'e',
                  299 .. 300 => 'f',
                  others     => 'a');
            begin
               pragma Assert (X /= X);
            end;

         --------------
         --  GROUP 5 --
         --------------

         when 51 =>
            declare
               --  "Short" string with an unprintable character.
               X : String := "baaaa" & ASCII.SOH & "aaaaaaaaaaaacdeff";
            begin
               pragma Assert (X /= X);
            end;

         when 52 =>
            --  TODO Enable this case after eng/spark/spark2014#1032 is fixed.
            --  See the latter issue for a dedicated test with this pattern.
            --
            --  declare
            --     --  The same string as above, aggregate notation, no 'others'.
            --     X : String :=
            --       (1        => 'b',
            --        2 .. 5   => 'a',
            --        6        => ASCII.SOH,
            --        7 .. 19  => 'a',
            --        20       => 'd',
            --        21       => 'e',
            --        22 .. 23 => 'f');
            --  begin
            --     pragma Assert (X /= X);
            --  end;
            null;

         when 53 =>
            --  TODO Enable this case after eng/spark/spark2014#1032 is fixed.
            --  See the latter issue for a dedicated test with this pattern.
            --
            --  declare
            --     --  "Long" string literal with an unprintable character that
            --     --  occurs beyond the truncation limit. No others.
            --     X : String (1 .. 2 * Str_Trunc_Limit) :=
            --       (1                                          => 'a',
            --        2 .. Str_Trunc_Limit + 2                   => 'b',
            --        Str_Trunc_Limit + 3 .. 2 * Str_Trunc_Limit => ASCII.SOH);
            --  begin
            --     pragma Assert (X /= X);
            --  end;
            null;

         when 54 =>
            --  TODO Enable this case after eng/spark/spark2014#1032 is fixed.
            --  See the latter issue for a dedicated test with this pattern.
            --
            --  declare
            --     --  "Long" string literal with an unprintable character that
            --     --  occurs before the truncation limit. No others.
            --     X : String (1 .. 2 * Str_Trunc_Limit) :=
            --       (1 => 'a', 2 => ASCII.SOH, 3 .. 2 * Str_Trunc_Limit => 'b');
            --  begin
            --     pragma Assert (X /= X);
            --  end;
            null;

         when 55 =>
            --  TODO Enable this case after eng/spark/spark2014#1032 is fixed.
            --  See the latter issue for a dedicated test with this pattern.
            --
            --  declare
            --     --  "Long" string literal with an unprintable character that
            --     --  occurs beyond the truncation limit. With others.
            --     X : String (1 .. 2 * Str_Trunc_Limit) :=
            --       (1                        => 'a',
            --        2 .. Str_Trunc_Limit + 2 => 'b',
            --        others                   => ASCII.SOH);
            --  begin
            --     pragma Assert (X /= X);
            --  end;
            null;

         when 56 =>
            --  TODO Enable this case after eng/spark/spark2014#1032 is fixed.
            --  See the latter issue for a dedicated test with this pattern.
            --
            --  declare
            --     --  "Long" string literal with an unprintable character that
            --     --  occurs before the truncation limit. With others.
            --     X : String (1 .. 2 * Str_Trunc_Limit) :=
            --       (1 => 'a', 2 => ASCII.SOH, others => 'b');
            --  begin
            --     pragma Assert (X /= X);
            --  end;
            null;

         when others =>
            null;
      end case;
   end;

end Array_Comparison_Str;
