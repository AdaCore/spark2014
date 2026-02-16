package body Array_Comparison_Str is

   pragma Warnings (Off, "analyzing unreferenced procedure *");
   pragma Warnings (Off, "subprogram * has no effect");

   --  Should be the same value that is chosen in the implementation. See
   --  CE_Max_Print_Chars_String in ce_pretty_printing.adb.
   Str_Trunc_Limit : constant := 30;

   --  Note: In the implementation string literals get treated as having an
   --  implicit 'others' => 'a'. This is not the case for aggregates where
   --  the presence and value of the 'others' is taken to be the same as in
   --  the aggregate.

   --------------
   --  GROUP 1 --
   --------------

   procedure P_10 is
      --  "Short" string with less than 15 'a' characters.
      X : String := "abacadaea";
   begin
      pragma Assert (X /= X);
   end P_10;

   procedure P_12 is
      --  "Short" string with no 'a' characters.
      X : String := "XbXcXdXeX";
   begin
      pragma Assert (X /= X);
   end;

   procedure P_13 is
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

   procedure P_21 is
      --  "Short" string with more than 15 'a' characters.
      X : String := "baaaaaaaaaaaaaaaaac";
   begin
      pragma Assert (X /= X);
   end;

   procedure P_22 is
      --  The same string as above, aggregate notation, no 'others'.
      X : String := (1 => 'b', 2 .. 18 => 'a', 19 => 'c');
   begin
      pragma Assert (X /= X);
   end;

   procedure P_23 is
      --  The same string as above, explicit 'others'.
      X : String (1 .. 19) := (1 => 'b', 19 => 'c', others => 'a');
   begin
      pragma Assert (X /= X);
   end;

   --------------
   --  GROUP 3 --
   --------------

   procedure P_31 is
      --  "Short" string with more than 15 'a' characters and more
      --  than 5 unique elements, string notation.
      X : String := "baaaaaaaaaaaaaaaaacdeff";
   begin
      pragma Assert (X /= X);
   end;

   procedure P_32 is
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

   procedure P_33 is
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

   procedure P_41 is
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

   procedure P_42 is
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

   procedure P_43 is
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

   procedure P_44 is
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

   procedure P_51a is
      --  "Short" string with an unprintable character and lots of 'a'-s.
      X : String := "baaaa" & ASCII.SOH & "aaaaaaaaaaaacdeff";
   begin
      pragma Assert (X /= X);
   end;

   procedure P_51b is
      --  "Short" string with an unprintable character and no 'a'-s.
      X : String := "bcccc" & ASCII.SOH & "cccccccccccccdeff";
   begin
      pragma Assert (X /= X);
   end;

   procedure P_52 is
      --  The same string as above, aggregate notation, no 'others'.
      X : String :=
        (1        => 'b',
         2 .. 5   => 'c',
         6        => ASCII.SOH,
         7 .. 19  => 'c',
         20       => 'd',
         21       => 'e',
         22 .. 23 => 'f');
   begin
      pragma Assert (X /= X);
   end;

   procedure P_53 is
      --  "Long" string literal with an unprintable character that
      --  occurs beyond the truncation limit. No others.
      X : String (1 .. 2 * Str_Trunc_Limit) :=
        (1                                          => 'a',
         2 .. Str_Trunc_Limit + 2                   => 'b',
         Str_Trunc_Limit + 3 .. 2 * Str_Trunc_Limit => ASCII.SOH);
   begin
      pragma Assert (X /= X);
   end;

   procedure P_54 is
      --  "Long" string literal with an unprintable character that
      --  occurs before the truncation limit. No others.
      X : String (1 .. 2 * Str_Trunc_Limit) :=
        (1 => 'a', 2 => ASCII.SOH, 3 .. 2 * Str_Trunc_Limit => 'b');
   begin
      pragma Assert (X /= X);
   end;

   procedure P_55 is
      --  "Long" string literal with an unprintable character that
      --  occurs beyond the truncation limit. With others.
      X : String (1 .. 2 * Str_Trunc_Limit) :=
        (1 => 'a', 2 .. Str_Trunc_Limit + 2 => 'b', others => ASCII.SOH);
   begin
      pragma Assert (X /= X);
   end;

   procedure P_56 is
      --  "Long" string literal with an unprintable character that
      --  occurs before the truncation limit. With others.
      X : String (1 .. 2 * Str_Trunc_Limit) :=
        (1 => 'a', 2 => ASCII.SOH, others => 'b');
   begin
      pragma Assert (X /= X);
   end;

   procedure P_Str (I : Integer) is begin null; end;

end Array_Comparison_Str;
