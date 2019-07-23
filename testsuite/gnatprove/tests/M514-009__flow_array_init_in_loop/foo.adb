package body Foo
is

   type Index_T is range 1 .. 10;

   type Array_T is array (Index_T) of Integer;
   type U_Array_T is array (Index_T range <>) of Integer;

   type Record_T is record
      A : Array_T;
      B : Boolean;
   end record;

   type M_Array_T is array (Index_T, Index_T) of Integer;

   procedure Test_01_Ok (R : out Record_T)
   is
   begin
      for I in Index_T loop
         R.A (I) := Integer (I);
      end loop;
      R.B := False;
   end Test_01_Ok;

   procedure Test_02_Ok_Hard (A : out U_Array_T)
   is
   begin
      for I in A'Range loop
         A (I) := Integer (I);
      end loop;
   end Test_02_Ok_Hard;

   procedure Test_03_E (A : out Array_T)
   is
   begin
      for I in Index_T loop
         A (I) := A (I);      -- @INITIALIZED:CHECK
      end loop;
   end Test_03_E;

   procedure Test_04_E (A : out Array_T) -- @INITIALIZED:CHECK
   is
   begin
      for I in Index_T loop
         if I > 5 then
            A (I) := 0;
         end if;
      end loop;
   end Test_04_E;

   procedure Test_05_Ok (A : out Array_T)
   is
   begin
      for I in Index_T loop
         if I > 5 then
            A (I) := 0;
         else
            A (I) := 1;
         end if;
      end loop;
   end Test_05_Ok;

   procedure Test_06_E (A : out Array_T)
   is
   begin
      for I in Index_T loop
         if A (I) > 5 then  -- @INITIALIZED:CHECK
            A (I) := 0;
         else
            A (I) := 1;
         end if;
      end loop;
   end Test_06_E;

   procedure Test_07_E (A :    out Array_T;
                        B : in     Array_T;
                        C : in out Boolean)
   is
   begin
      for I in Index_T loop
         A (I) := 0;
         if A = B then -- @INITIALIZED:CHECK
            C := True;
         end if;
      end loop;
   end Test_07_E;

   procedure Test_07_Ok_Hard (A : out Array_T)
   is
   begin
      for I in Index_T loop
         A (I) := 5;
         pragma Loop_Invariant (for all N in Index_T range Index_T'First .. I
                                  => A (N) > 0);
      end loop;
   end Test_07_Ok_Hard;

   procedure Test_08_E (A : out Array_T)
   is
   begin
      for I in Index_T loop
         A (I) := 0;
         A (I) := A (I + 1);
      end loop;
   end Test_08_E;

   procedure Test_09_E (A : out Array_T)
   is
   begin
      for I in Index_T loop
         A (I) := 0;
         if I > 5 then
            return;
         end if;
      end loop;
   end Test_09_E;

   procedure Test_10_Ok (A : out M_Array_T)
   is
   begin
      for I in Index_T loop
         for J in Index_T loop
            A (I, J) := Integer (I) + Integer (J);
         end loop;
      end loop;
   end Test_10_Ok;

   procedure Test_11_Ok (A : out M_Array_T)
   is
   begin
      for J in Index_T loop
         for I in Index_T loop
            if I < 5 then
               A (I, J) := Integer (I) + Integer (J);
            else
               A (I, J) := 0;
            end if;
         end loop;
      end loop;
   end Test_11_Ok;

   procedure Test_12_E (A : out M_Array_T)
   is
   begin
      for I in Index_T loop
         A (I, I) := Integer (I);
      end loop;
   end Test_12_E;

   procedure Test_13_E (A : out M_Array_T)
   is
   begin
      for I in Index_T loop
         A (I, 1) := Integer (I);
      end loop;
   end Test_13_E;

   procedure Test_14_E (A : out Array_T;
                        B : out Integer)
   is
   begin
      for I in Index_T loop
         A (I) := 0;
         B     := A (I + 1); -- @INITIALIZED:CHECK
      end loop;
   end Test_14_E;

   procedure Test_15_Ok_Hard (A : out Array_T;
                              B : out Integer)
   is
   begin
      for I in Index_T loop
         A (I) := 0;
         B     := A (I);
      end loop;
   end Test_15_Ok_Hard;

   procedure Test_15_E (A : out Array_T)
   is
   begin
      for I in Index_T range 2 .. Index_T'Last loop
         A (I) := 0;
      end loop;
   end Test_15_E;

   procedure Test_16_E (A : out Array_T; -- @INITIALIZED:CHECK
                        N :     Index_T)
   is
   begin
      for I in Index_T range Index_T'First .. N loop
         A (I) := 0;
      end loop;
   end Test_16_E;

   procedure Test_17_Maybe (A : out Array_T)
   is
   begin
      for I in 1 .. 10 loop
         A (Index_T (I)) := 0;
      end loop;
   end Test_17_Maybe;

   procedure Test_18_E (A : out M_Array_T)
   is
   begin
      for J in Index_T loop
         for I in Index_T loop
            A (I, J) := Integer (I) + Integer (J);
            exit when I = 5;
         end loop;
      end loop;
   end Test_18_E;

   procedure Test_19_Ok (A : out M_Array_T)
   is
   begin
      for J in Index_T loop
         for I in Index_T loop
            if I < 5 then
               A (I, J) := 0;
            else
               A (I, J) := 0;
            end if;
         end loop;
      end loop;
   end Test_19_Ok;

   procedure Test_20_Ok (A : out Array_T)
   is
   begin
      for I in reverse Index_T loop
         A (I) := 0;
      end loop;
   end Test_20_Ok;

   procedure Test_21_Ok (A : out Array_T)
   is
   begin
      for I in reverse Index_T range 1 .. 10 loop
         A (I) := 0;
      end loop;
   end Test_21_Ok;

   procedure Test_22_Ok (A : out Array_T)
   is
   begin
      for I in reverse Index_T range 1 .. 10 loop
         for J in reverse Index_T range 1 .. 5 loop
            A (J) := 5;
         end loop;
         A (I) := 1;
      end loop;
   end Test_22_Ok;

end Foo;
