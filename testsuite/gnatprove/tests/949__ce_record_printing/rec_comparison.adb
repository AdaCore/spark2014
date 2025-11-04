package body Rec_Comparison is

   pragma Warnings (Off, "analyzing unreferenced procedure *");
   pragma Warnings (Off, "subprogram * has no effect");

   type Natural_Array is array (Integer range <>) of Natural;

   procedure P_Rec (I : Integer) is

   begin

      case I is

         --------------
         --  GROUP 1 --
         --------------

         when 11 =>
            declare
               --  "Short" record, no 'others'.
               type R is record
                  F1 : Integer;
                  F2 : Integer;
                  F3 : Integer;
               end record;

               X : R := (F1 => 1, F2 => 2, F3 => 3);
            begin
               pragma Assert (X /= X);
            end;

         when 12 =>
            declare
               --  The same record as above, with 'others'.
               type R is record
                  F1 : Integer;
                  F2 : Integer;
                  F3 : Integer;
               end record;

               X : R := (F1 => 1, others => 5);
            begin
               pragma Assert (X /= X);
            end;

         --------------
         --  GROUP 2 --
         --------------

         when 21 =>
            declare
               --  "Long" record, no 'others'.
               type R is record
                  F1  : Integer;
                  F2  : Integer;
                  F3  : Integer;
                  F4  : Integer;
                  F5  : Integer;
                  F6  : Integer;
                  F7  : Integer;
                  F8  : Integer;
                  F9  : Integer;
                  F10 : Integer;
                  F11 : Integer;
                  F12 : Integer;
               end record;

               X : R :=
                 (F1  => 1,
                  F2  => 2,
                  F3  => 3,
                  F4  => 4,
                  F5  => 5,
                  F6  => 6,
                  F7  => 7,
                  F8  => 8,
                  F9  => 9,
                  F10 => 10,
                  F11 => 11,
                  F12 => 12);
            begin
               pragma Assert (X /= X);
            end;

         when 22 =>
            declare
               --  The same as above, with 'others'.
               type R is record
                  F1  : Integer;
                  F2  : Integer;
                  F3  : Integer;
                  F4  : Integer;
                  F5  : Integer;
                  F6  : Integer;
                  F7  : Integer;
                  F8  : Integer;
                  F9  : Integer;
                  F10 : Integer;
                  F11 : Integer;
                  F12 : Integer;
               end record;

               X : R := (F1 => 1, F2 => 2, others => 5);
            begin
               pragma Assert (X /= X);
            end;

         --------------
         --  GROUP 3 --
         --------------

         when 31 =>
            declare
               --  "Long" record containing "long" array, no 'others'.
               type R is record
                  F1  : Integer;
                  F2  : Integer;
                  F3  : Natural_Array (1 .. 300);
                  F4  : Integer;
                  F5  : Integer;
                  F6  : Integer;
                  F7  : Integer;
                  F8  : Integer;
                  F9  : Integer;
                  F10 : Integer;
                  F11 : Integer;
                  F12 : Integer;
               end record;

               X : R :=
                 (F1  => 1,
                  F2  => 2,
                  F3  =>
                    (1          => 1,
                     2 .. 18    => 2,
                     19         => 3,
                     20         => 4,
                     21 .. 298  => 5,
                     299 .. 300 => 6),
                  F4  => 4,
                  F5  => 5,
                  F6  => 6,
                  F7  => 7,
                  F8  => 8,
                  F9  => 9,
                  F10 => 10,
                  F11 => 11,
                  F12 => 12);
            begin
               pragma Assert (X /= X);
            end;

         when 32 =>
            declare
               --  The same as above, with 2x'others'.
               type R is record
                  F1  : Integer;
                  F2  : Integer;
                  F3  : Natural_Array (1 .. 300);
                  F4  : Integer;
                  F5  : Integer;
                  F6  : Integer;
                  F7  : Integer;
                  F8  : Integer;
                  F9  : Integer;
                  F10 : Integer;
                  F11 : Integer;
                  F12 : Integer;
               end record;

               X : R :=
                 (F1     => 1,
                  F2     => 2,
                  F3     =>
                    (1          => 1,
                     19         => 3,
                     20         => 4,
                     21 .. 298  => 5,
                     299 .. 300 => 6,
                     others     => 2),
                  others => 5);
            begin
               pragma Assert (X /= X);
            end;

         --------------
         --  GROUP 4 --
         --------------

         when 41 =>
            declare
               --  "Short" nested record containing "long" array, no 'others'.
               type R is record
                  F1  : Integer;
                  F2  : Integer;
                  F3  : Natural_Array (1 .. 300);
                  F4  : Integer;
                  F5  : Integer;
                  F6  : Integer;
                  F7  : Integer;
                  F8  : Integer;
                  F9  : Integer;
                  F10 : Integer;
                  F11 : Integer;
                  F12 : Integer;
               end record;

               type AR is array (Positive range <>) of R;

               type RAR is record
                  FF1 : Integer;
                  FF2 : AR (1 .. 30);
                  FF3 : Integer;
               end record;

               X_R : R :=
                 (F1  => 1,
                  F2  => 2,
                  F3  =>
                    (1          => 1,
                     2 .. 18    => 2,
                     19         => 3,
                     20         => 4,
                     21 .. 298  => 5,
                     299 .. 300 => 6),
                  F4  => 4,
                  F5  => 5,
                  F6  => 6,
                  F7  => 7,
                  F8  => 8,
                  F9  => 9,
                  F10 => 10,
                  F11 => 11,
                  F12 => 12);

               X_AR : AR := (1 .. 30 => X_R);

               X : RAR := (FF1 => 1, FF2 => X_AR, FF3 => 1);
            begin
               pragma Assert (X /= X);
            end;

         when 42 =>
            declare
               --  The same as above, with 3x'others'.
               type R is record
                  F1  : Integer;
                  F2  : Integer;
                  F3  : Natural_Array (1 .. 300);
                  F4  : Integer;
                  F5  : Integer;
                  F6  : Integer;
                  F7  : Integer;
                  F8  : Integer;
                  F9  : Integer;
                  F10 : Integer;
                  F11 : Integer;
                  F12 : Integer;
               end record;

               type AR is array (Positive range <>) of R;

               type RAR is record
                  FF1  : Integer;
                  FF2  : AR (1 .. 30);
                  FF3  : Integer;
                  FF4  : Integer;
                  FF5  : Integer;
                  FF6  : Integer;
                  FF7  : Integer;
                  FF8  : Integer;
                  FF9  : Integer;
                  FF10 : Integer;
                  FF11 : Integer;
                  FF12 : Integer;
               end record;

               X_R : R :=
                 (F1     => 1,
                  F2     => 2,
                  F3     =>
                    (1          => 1,
                     2 .. 18    => 2,
                     19         => 3,
                     20         => 4,
                     21 .. 298  => 5,
                     299 .. 300 => 6),
                  F4     => 4,
                  others => 111);

               X_AR : AR (1 .. 30) := (others => X_R);

               X : RAR := (FF2 => X_AR, others => 1);
            begin
               pragma Assert (X /= X);
            end;

         when others =>
            null;
      end case;
   end;

end Rec_Comparison;
