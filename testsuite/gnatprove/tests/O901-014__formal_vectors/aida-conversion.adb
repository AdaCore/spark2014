package body Aida.Conversion is
   pragma SPARK_Mode;

   function Convert_Character_Digit_To_Integer (Source : in  Character) return Integer is
   begin
      return Character'Pos (Source) - Character'Pos ('0');
   end Convert_Character_Digit_To_Integer;

   procedure Convert_Character_Digit_To_Integer (Source : in  Character;
                                                 Target : out Integer) is
   begin
      Target := Character'Pos (Source) - Character'Pos ('0');
   end Convert_Character_Digit_To_Integer;

   procedure Convert_String_To_Integer_Non_Negative_Case (Source     : in  String;
                                                          Target     : out Integer;
                                                          Has_Failed : out Boolean) with
     Pre => (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))) and 1 <= Source'Length and Source'Length <= 10,
     Contract_Cases => (Source'Length = 1 => Has_Failed = False and Target = Convert_Character_Digit_To_Integer(Source (Source'First)),
                        2 <= Source'Length and Source'Length <= 9 => Has_Failed = False,
                        Source'Length = 10 => (if ((Source(Source'First + 0) = '2' and
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
                                                       else
                                                         Has_Failed = True));

   procedure Convert_String_To_Integer_Negative_Case (Source     : in  String;
                                                      Target     : out Integer;
                                                      Has_Failed : out Boolean) with
     Pre => (Source'Length <= 11 and (2 <= Source'Length and then ((Source (Source'First) = '-') and
               (for all Index in Integer range (Source'First + 1) .. Source'Last => Aida.Characters.Is_Digit (Source (Index)))))),
     Contract_Cases => (Source'Length >=2 and Source'Length <= 10 => Has_Failed = False,
                        Source'Length = 11 => (if ((Source(Source'First + 1) = '2' and
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
                                                      (Source(Source'First + 1) < '2'))
                                                   then
                                                     Has_Failed = False
                                                       else
                                                         Has_Failed = True));

   procedure Convert_String_To_Integer (Source     : in  String;
                                        Target     : out Integer;
                                        Has_Failed : out Boolean) is
   begin
      if Source'Length = 0 then
         Target := 0;
         Has_Failed := True;
         return;
      end if;

      if Source (Source'First) = '-' then
         if Source'Length > 11 then
            Target := 0;
            Has_Failed := True;
            return;
         end if;

         if Source'Length = 1 then
            Target := 0;
            Has_Failed := True;
            return;
         end if;

         for I in Integer range (Source'First + 1)..Source'Last loop
            if not Aida.Characters.Is_Digit (Source(I)) then
               Target := 0;
               Has_Failed := True;
               return;
            end if;
            pragma Loop_Invariant (for all J in (Source'First + 1)..I => Aida.Characters.Is_Digit (Source(J)));
         end loop;

         Convert_String_To_Integer_Negative_Case (Source,
                                                  Target,
                                                  Has_Failed);
      else
         if Source'Length > 10 then
            Target := 0;
            Has_Failed := True;
            return;
         end if;

         for I in Integer range Source'First..Source'Last loop
            if not Aida.Characters.Is_Digit (Source(I)) then
               Target := 0;
               Has_Failed := True;
               return;
            end if;
            pragma Loop_Invariant (for all J in Source'First..I => Aida.Characters.Is_Digit (Source(J)));
         end loop;

         Convert_String_To_Integer_Non_Negative_Case (Source,
                                                      Target,
                                                      Has_Failed);
      end if;
   end Convert_String_To_Integer;

   procedure Calculate_Positive_Target_For_Length_10_Case_2_147_483_647 (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean) with
     Pre  => (Source'Length = 10 and then (Source(Source'First + 0) = '2' and
                Source(Source'First + 1) = '1' and
                Source(Source'First + 2) = '4' and
                Source(Source'First + 3) = '7' and
                Source(Source'First + 4) = '4' and
                Source(Source'First + 5) = '8' and
                Source(Source'First + 6) = '3' and
                Source(Source'First + 7) = '6' and
                Source(Source'First + 8) = '4' and
                Source(Source'First + 9) < '8')) and
     (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))),
     Post => Has_Failed = False;

   procedure Calculate_Positive_Target_For_Length_10_Case_2_147_483_647 (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range Source'First..(Source'First + 9)) of Integer :=
        (2, 1, 4, 7, 4, 8, 3, 6, 4, 7) with Ghost;

      type Number_Array_Type is array (Integer range Source'First..(Source'First + 9)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range Source'First..(Source'First + 9) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in Source'First..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in Source'First..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := N(Source'First + 9);
      pragma Assert (Target <= 7);

      Target := Target + 2_147_483_640;
      pragma Assert (Target <= 2_147_483_647);

      Has_Failed := False;
   end Calculate_Positive_Target_For_Length_10_Case_2_147_483_647;

   procedure Calculate_Positive_Target_For_Length_10_Case_2_147_483_63X (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean) with
     Pre  => (Source'Length = 10 and then (Source(Source'First + 0) = '2' and
                Source(Source'First + 1) = '1' and
                Source(Source'First + 2) = '4' and
                Source(Source'First + 3) = '7' and
                Source(Source'First + 4) = '4' and
                Source(Source'First + 5) = '8' and
                Source(Source'First + 6) = '3' and
                Source(Source'First + 7) = '6' and
                Source(Source'First + 8) < '4')) and
     (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))),
     Post => Has_Failed = False;

   procedure Calculate_Positive_Target_For_Length_10_Case_2_147_483_63X (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range Source'First..(Source'First + 9)) of Integer :=
        (2, 1, 4, 7, 4, 8, 3, 6, 3, 9) with Ghost;

      type Number_Array_Type is array (Integer range Source'First..(Source'First + 9)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range Source'First..(Source'First + 9) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in Source'First..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in Source'First..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := N(Source'First + 9);
      pragma Assert (Target <= 9);

      Target := Target + N(Source'First + 8) *            10;
      pragma Assert (Target <= 39);

      Target := Target + 2_147_483_600;
      pragma Assert (Target <= 2_147_483_639);

      Has_Failed := False;
   end Calculate_Positive_Target_For_Length_10_Case_2_147_483_63X;

   procedure Calculate_Positive_Target_For_Length_10_Case_2_147_483_5XX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean) with
     Pre  => (Source'Length = 10 and then (Source(Source'First + 0) <= '2' and
                Source(Source'First + 1) = '1' and
                Source(Source'First + 2) = '4' and
                Source(Source'First + 3) = '7' and
                Source(Source'First + 4) = '4' and
                Source(Source'First + 5) = '8' and
                Source(Source'First + 6) = '3' and
                Source(Source'First + 7) < '6')) and
     (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))),
     Post => Has_Failed = False;

   procedure Calculate_Positive_Target_For_Length_10_Case_2_147_483_5XX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range Source'First..(Source'First + 9)) of Integer :=
        (2, 1, 4, 7, 4, 8, 3, 5, 9, 9) with Ghost;

      type Number_Array_Type is array (Integer range Source'First..(Source'First + 9)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range Source'First..(Source'First + 9) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in Source'First..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in Source'First..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := N(Source'First + 9);
      pragma Assert (Target <= 9);

      Target := Target + N(Source'First + 8) *            10;
      pragma Assert (Target <= 99);

      Target := Target + N(Source'First + 7) *           100;
      pragma Assert (Target <= 599);

      Target := Target + 2_147_483_000;
      pragma Assert (Target <= 2_147_483_599);

      Has_Failed := False;
   end Calculate_Positive_Target_For_Length_10_Case_2_147_483_5XX;

   procedure Calculate_Positive_Target_For_Length_10_Case_2_147_482_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean) with
     Pre  => (Source'Length = 10 and then (Source(Source'First + 0) = '2' and
                Source(Source'First + 1) = '1' and
                Source(Source'First + 2) = '4' and
                Source(Source'First + 3) = '7' and
                Source(Source'First + 4) = '4' and
                Source(Source'First + 5) = '8' and
                Source(Source'First + 6) < '3')) and
     (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))),
     Post => Has_Failed = False;

   procedure Calculate_Positive_Target_For_Length_10_Case_2_147_482_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range Source'First..(Source'First + 9)) of Integer :=
        (2, 1, 4, 7, 4, 8, 2, 9, 9, 9) with Ghost;

      type Number_Array_Type is array (Integer range Source'First..(Source'First + 9)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range Source'First..(Source'First + 9) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in Source'First..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in Source'First..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := N(Source'First + 9);
      pragma Assert (Target <= 9);

      Target := Target + N(Source'First + 8) *            10;
      pragma Assert (Target <= 99);

      Target := Target + N(Source'First + 7) *           100;
      pragma Assert (Target <= 999);

      Target := Target + N(Source'First + 6) *         1_000;
      pragma Assert (Target <= 2_999);

      Target := Target + 2_147_480_000;
      pragma Assert (Target <= 2_147_482_999);

      Has_Failed := False;
   end Calculate_Positive_Target_For_Length_10_Case_2_147_482_XXX;

   procedure Calculate_Positive_Target_For_Length_10_Case_2_147_47X_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean) with
     Pre  => (Source'Length = 10 and then (Source(Source'First + 0) = '2' and
                Source(Source'First + 1) = '1' and
                Source(Source'First + 2) = '4' and
                Source(Source'First + 3) = '7' and
                Source(Source'First + 4) = '4' and
                Source(Source'First + 5) < '8')) and
     (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))),
     Post => Has_Failed = False;

   procedure Calculate_Positive_Target_For_Length_10_Case_2_147_47X_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range Source'First..(Source'First + 9)) of Integer :=
        (2, 1, 4, 7, 4, 7, 9, 9, 9, 9) with Ghost;

      type Number_Array_Type is array (Integer range Source'First..(Source'First + 9)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range Source'First..(Source'First + 9) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in Source'First..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in Source'First..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := N(Source'First + 9);
      pragma Assert (Target <= 9);

      Target := Target + N(Source'First + 8) *            10;
      pragma Assert (Target <= 99);

      Target := Target + N(Source'First + 7) *           100;
      pragma Assert (Target <= 999);

      Target := Target + N(Source'First + 6) *         1_000;
      pragma Assert (Target <= 9_999);

      Target := Target + N(Source'First + 5) *        10_000;
      pragma Assert (Target <= 79_999);

      Target := Target + 2_147_400_000;
      pragma Assert (Target <= 2_147_479_999);

      Has_Failed := False;
   end Calculate_Positive_Target_For_Length_10_Case_2_147_47X_XXX;

   procedure Calculate_Positive_Target_For_Length_10_Case_2_147_3XX_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean) with
     Pre  => (Source'Length = 10 and then (Source(Source'First + 0) = '2' and
                Source(Source'First + 1) = '1' and
                Source(Source'First + 2) = '4' and
                Source(Source'First + 3) = '7' and
                Source(Source'First + 4) < '4')) and
     (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))),
     Post => Has_Failed = False;

   procedure Calculate_Positive_Target_For_Length_10_Case_2_147_3XX_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range Source'First..(Source'First + 9)) of Integer :=
        (2, 1, 4, 7, 3, 9, 9, 9, 9, 9) with Ghost;

      type Number_Array_Type is array (Integer range Source'First..(Source'First + 9)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range Source'First..(Source'First + 9) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in Source'First..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in Source'First..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := N(Source'First + 9);
      pragma Assert (Target <= 9);

      Target := Target + N(Source'First + 8) *            10;
      pragma Assert (Target <= 99);

      Target := Target + N(Source'First + 7) *           100;
      pragma Assert (Target <= 999);

      Target := Target + N(Source'First + 6) *         1_000;
      pragma Assert (Target <= 9_999);

      Target := Target + N(Source'First + 5) *        10_000;
      pragma Assert (Target <= 99_999);

      Target := Target + N(Source'First + 4) *       100_000;
      pragma Assert (Target <= 399_999);

      Target := Target + 2_147_000_000;
      pragma Assert (Target <= 2_147_399_999);

      Has_Failed := False;
   end Calculate_Positive_Target_For_Length_10_Case_2_147_3XX_XXX;

   procedure Calculate_Positive_Target_For_Length_10_Case_2_146_XXX_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean) with
     Pre  => (Source'Length = 10 and then (Source(Source'First + 0) = '2' and
                Source(Source'First + 1) = '1' and
                Source(Source'First + 2) = '4' and
                Source(Source'First + 3) < '7')) and
     (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))),
     Post => Has_Failed = False;

   procedure Calculate_Positive_Target_For_Length_10_Case_2_146_XXX_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range Source'First..(Source'First + 9)) of Integer :=
        (2, 1, 4, 6, 9, 9, 9, 9, 9, 9) with Ghost;

      type Number_Array_Type is array (Integer range Source'First..(Source'First + 9)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range Source'First..(Source'First + 9) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in Source'First..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in Source'First..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := N(Source'First + 9);
      pragma Assert (Target <= 9);

      Target := Target + N(Source'First + 8) *            10;
      pragma Assert (Target <= 99);

      Target := Target + N(Source'First + 7) *           100;
      pragma Assert (Target <= 999);

      Target := Target + N(Source'First + 6) *         1_000;
      pragma Assert (Target <= 9_999);

      Target := Target + N(Source'First + 5) *        10_000;
      pragma Assert (Target <= 99_999);

      Target := Target + N(Source'First + 4) *       100_000;
      pragma Assert (Target <= 999_999);

      Target := Target + N(Source'First + 3) *     1_000_000;
      pragma Assert (Target <= 6_999_999);

      Target := Target + 2_140_000_000;
      pragma Assert (Target <= 2_146_999_999);

      Has_Failed := False;
   end Calculate_Positive_Target_For_Length_10_Case_2_146_XXX_XXX;

   procedure Calculate_Positive_Target_For_Length_10_Case_2_13X_XXX_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean) with
     Pre  => (Source'Length = 10 and then (Source(Source'First + 0) = '2' and
                Source(Source'First + 1) = '1' and
                Source(Source'First + 2) < '4')) and
     (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))),
     Post => Has_Failed = False;

   procedure Calculate_Positive_Target_For_Length_10_Case_2_13X_XXX_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range Source'First..(Source'First + 9)) of Integer :=
        (2, 1, 3, 9, 9, 9, 9, 9, 9, 9) with Ghost;

      type Number_Array_Type is array (Integer range Source'First..(Source'First + 9)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range Source'First..(Source'First + 9) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in Source'First..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in Source'First..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := N(Source'First + 9);
      pragma Assert (Target <= 9);

      Target := Target + N(Source'First + 8) *            10;
      pragma Assert (Target <= 99);

      Target := Target + N(Source'First + 7) *           100;
      pragma Assert (Target <= 999);

      Target := Target + N(Source'First + 6) *         1_000;
      pragma Assert (Target <= 9_999);

      Target := Target + N(Source'First + 5) *        10_000;
      pragma Assert (Target <= 99_999);

      Target := Target + N(Source'First + 4) *       100_000;
      pragma Assert (Target <= 999_999);

      Target := Target + N(Source'First + 3) *     1_000_000;
      pragma Assert (Target <= 9_999_999);

      Target := Target + N(Source'First + 2) *    10_000_000;
      pragma Assert (Target <= 39_999_999);

      Target := Target + 2_100_000_000;
      pragma Assert (Target <= 2_139_999_999);

      Has_Failed := False;
   end Calculate_Positive_Target_For_Length_10_Case_2_13X_XXX_XXX;

   procedure Calculate_Positive_Target_For_Length_10_Case_2_0XX_XXX_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean) with
     Pre  => (Source'Length = 10 and then (Source(Source'First + 0) = '2' and
                Source(Source'First + 1) = '0')) and
     (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))),
     Post => Has_Failed = False;

   procedure Calculate_Positive_Target_For_Length_10_Case_2_0XX_XXX_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range Source'First..(Source'First + 9)) of Integer :=
        (2, 0, 9, 9, 9, 9, 9, 9, 9, 9) with Ghost;

      type Number_Array_Type is array (Integer range Source'First..(Source'First + 9)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range Source'First..(Source'First + 9) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in Source'First..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in Source'First..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := N(Source'First + 9);
      pragma Assert (Target <= 9);

      Target := Target + N(Source'First + 8) *            10;
      pragma Assert (Target <= 99);

      Target := Target + N(Source'First + 7) *           100;
      pragma Assert (Target <= 999);

      Target := Target + N(Source'First + 6) *         1_000;
      pragma Assert (Target <= 9_999);

      Target := Target + N(Source'First + 5) *        10_000;
      pragma Assert (Target <= 99_999);

      Target := Target + N(Source'First + 4) *       100_000;
      pragma Assert (Target <= 999_999);

      Target := Target + N(Source'First + 3) *     1_000_000;
      pragma Assert (Target <= 9_999_999);

      Target := Target + N(Source'First + 2) *    10_000_000;
      pragma Assert (Target <= 99_999_999);

      Target := Target + 2_000_000_000;
      pragma Assert (Target <= 2_099_999_999);

      Has_Failed := False;
   end Calculate_Positive_Target_For_Length_10_Case_2_0XX_XXX_XXX;

   procedure Calculate_Positive_Target_For_Length_10_Case_1_XXX_XXX_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean) with
     Pre  => (Source'Length = 10 and then (Source(Source'First + 0) < '2')) and
     (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))),
     Post => Has_Failed = False;

   procedure Calculate_Positive_Target_For_Length_10_Case_1_XXX_XXX_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean)
   is
      type Number_Array_Type is array (Integer range Source'First..(Source'First + 9)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range Source'First..(Source'First + 9) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all J in Source'First..Index => N(J) = Convert_Character_Digit_To_Integer (Source (J)));
      end loop;

      Target := N(Source'First + 9);
      pragma Assert (Target <= 9);

      Target := Target + N(Source'First + 8) *            10;
      pragma Assert (Target <= 99);

      Target := Target + N(Source'First + 7) *           100;
      pragma Assert (Target <= 999);

      Target := Target + N(Source'First + 6) *         1_000;
      pragma Assert (Target <= 9_999);

      Target := Target + N(Source'First + 5) *        10_000;
      pragma Assert (Target <= 99_999);

      Target := Target + N(Source'First + 4) *       100_000;
      pragma Assert (Target <= 999_999);

      Target := Target + N(Source'First + 3) *     1_000_000;
      pragma Assert (Target <= 9_999_999);

      Target := Target + N(Source'First + 2) *    10_000_000;
      pragma Assert (Target <= 99_999_999);

      Target := Target + N(Source'First + 1) *   100_000_000;
      pragma Assert (Target <= 999_999_999);

      Target := Target + 1_000_000_000;
      pragma Assert (Target <= 1_999_999_999);

      Has_Failed := False;
   end Calculate_Positive_Target_For_Length_10_Case_1_XXX_XXX_XXX;

   function Int (C : Character) return Integer renames Aida.Conversion.Convert_Character_Digit_To_Integer;

   procedure Calculate_Positive_Target_Length_9 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean) with
     Pre  => Source'Length = 9 and (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))),
     Post => Has_Failed = False and Target =
     Int (Source (Source'First + 0)) * 100_000_000 +
       Int (Source (Source'First + 1)) * 10_000_000 +
         Int (Source (Source'First + 2)) * 1_000_000 +
           Int (Source (Source'First + 3)) * 100_000 +
             Int (Source (Source'First + 4)) * 10_000 +
               Int (Source (Source'First + 5)) * 1_000 +
                 Int (Source (Source'First + 6)) * 100 +
                   Int (Source (Source'First + 7)) * 10 +
                     Int (Source (Source'First + 8)) * 1;

   procedure Calculate_Positive_Target_Length_9 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean)
   is
      type Number_Array_Type is array (Integer range Source'First..(Source'First + 8)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range Source'First..(Source'First + 8) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all J in Source'First..Index => N(J) = Convert_Character_Digit_To_Integer (Source (J)));
      end loop;

      Target := N(Source'First + 8);
      pragma Assert (Target <= 9);

      Target := Target + N(Source'First + 7) *            10;
      pragma Assert (Target <= 99);

      Target := Target + N(Source'First + 6) *           100;
      pragma Assert (Target <= 999);

      Target := Target + N(Source'First + 5) *         1_000;
      pragma Assert (Target <= 9_999);

      Target := Target + N(Source'First + 4) *        10_000;
      pragma Assert (Target <= 99_999);

      Target := Target + N(Source'First + 3) *       100_000;
      pragma Assert (Target <= 999_999);

      Target := Target + N(Source'First + 2) *     1_000_000;
      pragma Assert (Target <= 9_999_999);

      Target := Target + N(Source'First + 1) *    10_000_000;
      pragma Assert (Target <= 99_999_999);

      Target := Target + N(Source'First + 0) *   100_000_000;
      pragma Assert (Target <= 999_999_999);

      Has_Failed := False;
   end Calculate_Positive_Target_Length_9;

   procedure Calculate_Positive_Target_Length_8 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean) with
     Pre  => Source'Length = 8 and (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))),
     Post => Has_Failed = False  and Target =
     Int (Source (Source'First + 0)) * 10_000_000 +
       Int (Source (Source'First + 1)) * 1_000_000 +
         Int (Source (Source'First + 2)) * 100_000 +
           Int (Source (Source'First + 3)) * 10_000 +
             Int (Source (Source'First + 4)) * 1_000 +
               Int (Source (Source'First + 5)) * 100 +
                 Int (Source (Source'First + 6)) * 10 +
                   Int (Source (Source'First + 7)) * 1;

   procedure Calculate_Positive_Target_Length_8 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean)
   is
      type Number_Array_Type is array (Integer range Source'First..(Source'First + 7)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range Source'First..(Source'First + 7) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all J in Source'First..Index => N(J) = Convert_Character_Digit_To_Integer (Source (J)));
      end loop;

      Target := N(Source'First + 7);
      pragma Assert (Target <= 9);

      Target := Target + N(Source'First + 6) *            10;
      pragma Assert (Target <= 99);

      Target := Target + N(Source'First + 5) *           100;
      pragma Assert (Target <= 999);

      Target := Target + N(Source'First + 4) *         1_000;
      pragma Assert (Target <= 9_999);

      Target := Target + N(Source'First + 3) *        10_000;
      pragma Assert (Target <= 99_999);

      Target := Target + N(Source'First + 2) *       100_000;
      pragma Assert (Target <= 999_999);

      Target := Target + N(Source'First + 1) *     1_000_000;
      pragma Assert (Target <= 9_999_999);

      Target := Target + N(Source'First + 0) *    10_000_000;
      pragma Assert (Target <= 99_999_999);

      Has_Failed := False;
   end Calculate_Positive_Target_Length_8;

   procedure Calculate_Positive_Target_Length_7 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean) with
     Pre  => Source'Length = 7 and (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))),
     Post => Has_Failed = False  and Target =
       Int (Source (Source'First + 0)) * 1_000_000 +
         Int (Source (Source'First + 1)) * 100_000 +
           Int (Source (Source'First + 2)) * 10_000 +
             Int (Source (Source'First + 3)) * 1_000 +
               Int (Source (Source'First + 4)) * 100 +
                 Int (Source (Source'First + 5)) * 10 +
                   Int (Source (Source'First + 6)) * 1;

   procedure Calculate_Positive_Target_Length_7 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean)
   is
      type Number_Array_Type is array (Integer range Source'First..(Source'First + 6)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range Source'First..(Source'First + 6) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all J in Source'First..Index => N(J) = Convert_Character_Digit_To_Integer (Source (J)));
      end loop;

      Target := N(Source'First + 6);
      pragma Assert (Target <= 9);

      Target := Target + N(Source'First + 5) *            10;
      pragma Assert (Target <= 99);

      Target := Target + N(Source'First + 4) *           100;
      pragma Assert (Target <= 999);

      Target := Target + N(Source'First + 3) *         1_000;
      pragma Assert (Target <= 9_999);

      Target := Target + N(Source'First + 2) *        10_000;
      pragma Assert (Target <= 99_999);

      Target := Target + N(Source'First + 1) *       100_000;
      pragma Assert (Target <= 999_999);

      Target := Target + N(Source'First + 0) *     1_000_000;
      pragma Assert (Target <= 9_999_999);

      Has_Failed := False;
   end Calculate_Positive_Target_Length_7;

   procedure Calculate_Positive_Target_Length_6 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean) with
     Pre  => Source'Length = 6 and (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))),
     Post => Has_Failed = False  and Target =
         Int (Source (Source'First + 0)) * 100_000 +
           Int (Source (Source'First + 1)) * 10_000 +
             Int (Source (Source'First + 2)) * 1_000 +
               Int (Source (Source'First + 3)) * 100 +
                 Int (Source (Source'First + 4)) * 10 +
                   Int (Source (Source'First + 5)) * 1;

   procedure Calculate_Positive_Target_Length_6 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean)
   is
      type Number_Array_Type is array (Integer range Source'First..(Source'First + 5)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range Source'First..(Source'First + 5) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all J in Source'First..Index => N(J) = Convert_Character_Digit_To_Integer (Source (J)));
      end loop;

      Target := N(Source'First + 5);
      pragma Assert (Target <= 9);

      Target := Target + N(Source'First + 4) *            10;
      pragma Assert (Target <= 99);

      Target := Target + N(Source'First + 3) *           100;
      pragma Assert (Target <= 999);

      Target := Target + N(Source'First + 2) *         1_000;
      pragma Assert (Target <= 9_999);

      Target := Target + N(Source'First + 1) *        10_000;
      pragma Assert (Target <= 99_999);

      Target := Target + N(Source'First + 0) *       100_000;
      pragma Assert (Target <= 999_999);

      Has_Failed := False;
   end Calculate_Positive_Target_Length_6;

   procedure Calculate_Positive_Target_Length_5 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean) with
     Pre  => Source'Length = 5 and (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))),
     Post => Has_Failed = False  and Target =
           Int (Source (Source'First + 0)) * 10_000 +
             Int (Source (Source'First + 1)) * 1_000 +
               Int (Source (Source'First + 2)) * 100 +
                 Int (Source (Source'First + 3)) * 10 +
                   Int (Source (Source'First + 4)) * 1;

   procedure Calculate_Positive_Target_Length_5 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean)
   is
      type Number_Array_Type is array (Integer range Source'First..(Source'First + 4)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range Source'First..(Source'First + 4) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all J in Source'First..Index => N(J) = Convert_Character_Digit_To_Integer (Source (J)));
      end loop;

      Target := N(Source'First + 4);
      pragma Assert (Target <= 9);

      Target := Target + N(Source'First + 3) *            10;
      pragma Assert (Target <= 99);

      Target := Target + N(Source'First + 2) *           100;
      pragma Assert (Target <= 999);

      Target := Target + N(Source'First + 1) *         1_000;
      pragma Assert (Target <= 9_999);

      Target := Target + N(Source'First + 0) *        10_000;
      pragma Assert (Target <= 99_999);

      Has_Failed := False;
   end Calculate_Positive_Target_Length_5;

   procedure Calculate_Positive_Target_Length_4 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean) with
     Pre  => Source'Length = 4 and (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))),
     Post => Has_Failed = False  and Target =
       Int (Source (Source'First + 0)) * 1_000 +
         Int (Source (Source'First + 1)) * 100 +
           Int (Source (Source'First + 2)) * 10 +
             Int (Source (Source'First + 3)) * 1;

   procedure Calculate_Positive_Target_Length_4 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean)
   is
      type Number_Array_Type is array (Integer range Source'First..(Source'First + 3)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range Source'First..(Source'First + 3) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all J in Source'First..Index => N(J) = Convert_Character_Digit_To_Integer (Source (J)));
      end loop;

      Target := N(Source'First + 3);
      pragma Assert (Target <= 9);

      Target := Target + N(Source'First + 2) *            10;
      pragma Assert (Target <= 99);

      Target := Target + N(Source'First + 1) *           100;
      pragma Assert (Target <= 999);

      Target := Target + N(Source'First + 0) *         1_000;
      pragma Assert (Target <= 9_999);

      Has_Failed := False;
   end Calculate_Positive_Target_Length_4;

   procedure Calculate_Positive_Target_Length_3 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean) with
     Pre  => Source'Length = 3 and (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))),
     Post => Has_Failed = False  and Target =
     Int (Source (Source'First + 0)) * 100 +
       Int (Source (Source'First + 1)) * 10 +
         Int (Source (Source'First + 2)) * 1;

   procedure Calculate_Positive_Target_Length_3 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean)
   is
      type Number_Array_Type is array (Integer range Source'First..(Source'First + 2)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range Source'First..(Source'First + 2) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all J in Source'First..Index => N(J) = Convert_Character_Digit_To_Integer (Source (J)));
      end loop;

      Target := N(Source'First + 2);
      pragma Assert (Target <= 9);

      Target := Target + N(Source'First + 1) *            10;
      pragma Assert (Target <= 99);

      Target := Target + N(Source'First + 0) *           100;
      pragma Assert (Target <= 999);

      Has_Failed := False;
   end Calculate_Positive_Target_Length_3;

   procedure Calculate_Positive_Target_Length_2 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean) with
     Pre  => Source'Length = 2 and (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))),
     Post => Has_Failed = False and Target = Int (Source (Source'First + 0)) * 10 + Int (Source (Source'First + 1)),
     Depends => (Target => Source, Has_Failed => null);

   procedure Calculate_Positive_Target_Length_2 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean)
   is
      type Number_Array_Type is array (Integer range Source'First..(Source'First + 1)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range Source'First..(Source'First + 1) loop
         Convert_Character_Digit_To_Integer (Source => Source (Index),
                                             Target => N (Index));
         pragma Loop_Invariant (for all J in Source'First..Index => N(J) = Convert_Character_Digit_To_Integer (Source (J)));
      end loop;

      Target := N(Source'First + 1);
      pragma Assert (Target <= 9);

      Target := Target + N(Source'First + 0) * 10;
      pragma Assert (Target <= 99);

      Has_Failed := False;
   end Calculate_Positive_Target_Length_2;

   procedure Calculate_Positive_Target_Length_1 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean) with
     Pre  => Source'Length = 1 and (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))),
     Post => Has_Failed = False and Target = Int (Source (Source'First));

   procedure Calculate_Positive_Target_Length_1 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean) is
   begin
      Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Source'First),
                                                          Target => Target);

      pragma Assert (Target <= 9);

      Has_Failed := False;
   end Calculate_Positive_Target_Length_1;

   procedure Calculate_Positive_Target (Source     : in  String;
                                        Target     : out Integer;
                                        Has_Failed : out Boolean) with
     Pre  => Source'Length > 0 and Source'Length < 10 and (for all Index in Source'Range => Aida.Characters.Is_Digit (Source (Index))),
     Post => Has_Failed = False,
     Contract_Cases => (Source'Length = 1 => Target = Int (Source (Source'First)),
                        Source'Length = 2 => Target = Int (Source (Source'First + 0)) * 10 + Int (Source (Source'First + 1)),
                        Source'Length = 3 => Target = Int (Source (Source'First + 0)) * 100 + Int (Source (Source'First + 1)) * 10 + Int (Source (Source'First + 2)) * 1,
                        Source'Length = 4 => Target =
                          Int (Source (Source'First + 0)) * 1_000 +
                            Int (Source (Source'First + 1)) * 100 +
                          Int (Source (Source'First + 2)) * 10 +
                            Int (Source (Source'First + 3)) * 1,
                        Source'Length = 5 => Target =
                          Int (Source (Source'First + 0)) * 10_000 +
                            Int (Source (Source'First + 1)) * 1_000 +
                          Int (Source (Source'First + 2)) * 100 +
                            Int (Source (Source'First + 3)) * 10 +
                          Int (Source (Source'First + 4)) * 1,
                        Source'Length = 6 => Target =
                          Int (Source (Source'First + 0)) * 100_000 +
                            Int (Source (Source'First + 1)) * 10_000 +
                          Int (Source (Source'First + 2)) * 1_000 +
                            Int (Source (Source'First + 3)) * 100 +
                          Int (Source (Source'First + 4)) * 10 +
                            Int (Source (Source'First + 5)) * 1,
                        Source'Length = 7 => Target =
                          Int (Source (Source'First + 0)) * 1_000_000 +
                            Int (Source (Source'First + 1)) * 100_000 +
                          Int (Source (Source'First + 2)) * 10_000 +
                            Int (Source (Source'First + 3)) * 1_000 +
                          Int (Source (Source'First + 4)) * 100 +
                            Int (Source (Source'First + 5)) * 10 +
                          Int (Source (Source'First + 6)) * 1,
                        Source'Length = 8 => Target =
                          Int (Source (Source'First + 0)) * 10_000_000 +
                            Int (Source (Source'First + 1)) * 1_000_000 +
                          Int (Source (Source'First + 2)) * 100_000 +
                            Int (Source (Source'First + 3)) * 10_000 +
                          Int (Source (Source'First + 4)) * 1_000 +
                            Int (Source (Source'First + 5)) * 100 +
                          Int (Source (Source'First + 6)) * 10 +
                            Int (Source (Source'First + 7)) * 1,
                        Source'Length = 9 => Target =
                          Int (Source (Source'First + 0)) * 100_000_000 +
                            Int (Source (Source'First + 1)) * 10_000_000 +
                          Int (Source (Source'First + 2)) * 1_000_000 +
                            Int (Source (Source'First + 3)) * 100_000 +
                          Int (Source (Source'First + 4)) * 10_000 +
                            Int (Source (Source'First + 5)) * 1_000 +
                          Int (Source (Source'First + 6)) * 100 +
                            Int (Source (Source'First + 7)) * 10 +
                          Int (Source (Source'First + 8)) * 1);

   procedure Calculate_Positive_Target (Source     : in  String;
                                        Target     : out Integer;
                                        Has_Failed : out Boolean) is
   begin
      case Source'Length is
         when 1 =>
            Calculate_Positive_Target_Length_1 (Source,
                                                Target,
                                                Has_Failed);
         when 2 =>
            Calculate_Positive_Target_Length_2 (Source,
                                                Target,
                                                Has_Failed);
         when 3 =>
            Calculate_Positive_Target_Length_3 (Source,
                                                Target,
                                                Has_Failed);
         when 4 =>
            Calculate_Positive_Target_Length_4 (Source,
                                                Target,
                                                Has_Failed);
         when 5 =>
            Calculate_Positive_Target_Length_5 (Source,
                                                Target,
                                                Has_Failed);
         when 6 =>
            Calculate_Positive_Target_Length_6 (Source,
                                                Target,
                                                Has_Failed);
         when 7 =>
            Calculate_Positive_Target_Length_7 (Source,
                                                Target,
                                                Has_Failed);
         when 8 =>
            Calculate_Positive_Target_Length_8 (Source,
                                                Target,
                                                Has_Failed);
         when 9 =>
            Calculate_Positive_Target_Length_9 (Source,
                                                Target,
                                                Has_Failed);
         when others =>
            Target := 0;
            Has_Failed := True;
      end case;
   end Calculate_Positive_Target;

   procedure Convert_String_To_Integer_Non_Negative_Case (Source     : in  String;
                                                          Target     : out Integer;
                                                          Has_Failed : out Boolean) is
   begin
      Target := 0;

      if Source'Length = 10 then
         if Source (Source'First) > '2' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First) < '2' then
            Calculate_Positive_Target_For_Length_10_Case_1_XXX_XXX_XXX (Source,
                                                                        Target,
                                                                        Has_Failed);
            return;
         end if;

         if Source (Source'First + 1) > '1' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 1) < '1' then
            Calculate_Positive_Target_For_Length_10_Case_2_0XX_XXX_XXX (Source,
                                                                        Target,
                                                                        Has_Failed);
            return;
         end if;

         if Source (Source'First + 2) > '4' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 2) < '4' then
            Calculate_Positive_Target_For_Length_10_Case_2_13X_XXX_XXX (Source,
                                                                        Target,
                                                                        Has_Failed);
            return;
         end if;

         if Source (Source'First + 3) > '7' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 3) < '7' then
            Calculate_Positive_Target_For_Length_10_Case_2_146_XXX_XXX (Source,
                                                                        Target,
                                                                        Has_Failed);
            return;
         end if;

         if Source (Source'First + 4) > '4' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 4) < '4' then
            Calculate_Positive_Target_For_Length_10_Case_2_147_3XX_XXX (Source,
                                                                        Target,
                                                                        Has_Failed);
            return;
         end if;

         if Source (Source'First + 5) > '8' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 5) < '8' then
            Calculate_Positive_Target_For_Length_10_Case_2_147_47X_XXX (Source,
                                                                        Target,
                                                                        Has_Failed);
            return;
         end if;

         if Source (Source'First + 6) > '3' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 6) < '3' then
            Calculate_Positive_Target_For_Length_10_Case_2_147_482_XXX (Source,
                                                                        Target,
                                                                        Has_Failed);
            return;
         end if;

         if Source (Source'First + 7) > '6' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 7) < '6' then
            Calculate_Positive_Target_For_Length_10_Case_2_147_483_5XX (Source,
                                                                        Target,
                                                                        Has_Failed);
            return;
         end if;

         if Source (Source'First + 8) > '4' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 8) < '4' then
            Calculate_Positive_Target_For_Length_10_Case_2_147_483_63X (Source,
                                                                        Target,
                                                                        Has_Failed);
            return;
         end if;

         if Source (Source'First + 9) > '7' then
            Has_Failed := True;
            return;
         end if;

         Calculate_Positive_Target_For_Length_10_Case_2_147_483_647 (Source,
                                                                     Target,
                                                                     Has_Failed);
      else
         Calculate_Positive_Target (Source,
                                    Target,
                                    Has_Failed);
      end if;
   end Convert_String_To_Integer_Non_Negative_Case;

   procedure Calculate_Negative_Target_For_Length_11_Case_2_147_483_648 (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean) with
     Pre  => (Source'Length = 11 and then (Source(Source'First + 0) = '-' and
                Source(Source'First + 1) = '2' and
                Source(Source'First + 2) = '1' and
                Source(Source'First + 3) = '4' and
                Source(Source'First + 4) = '7' and
                Source(Source'First + 5) = '4' and
                Source(Source'First + 6) = '8' and
                Source(Source'First + 7) = '3' and
                Source(Source'First + 8) = '6' and
                Source(Source'First + 9) = '4' and
                Source(Source'First + 10) < '9' and
                (for all Index in (Source'First + 10)..(Source'First + 10) => Aida.Characters.Is_Digit (Source (Index))))),
     Post => Has_Failed = False;

   procedure Calculate_Negative_Target_For_Length_11_Case_2_147_483_648 (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean)
   is
      N : Integer;
   begin
      Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source(Source'First + 10),
                                                          Target => N);

      Target := -N;
      pragma Assert (Target >= -8);

      Target := Target - 2_147_483_640;
      pragma Assert (Target >= -2_147_483_648);

      Has_Failed := False;
   end Calculate_Negative_Target_For_Length_11_Case_2_147_483_648;

   procedure Calculate_Negative_Target_For_Length_11_Case_2_147_483_63X (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean) with
     Pre  => (Source'Length = 11 and then (Source(Source'First + 0) = '-' and
                Source(Source'First + 1) = '2' and
                Source(Source'First + 2) = '1' and
                Source(Source'First + 3) = '4' and
                Source(Source'First + 4) = '7' and
                Source(Source'First + 5) = '4' and
                Source(Source'First + 6) = '8' and
                Source(Source'First + 7) = '3' and
                Source(Source'First + 8) = '6' and
                Source(Source'First + 9) < '4' and
                (for all Index in (Source'First + 9)..(Source'First + 10) => Aida.Characters.Is_Digit (Source (Index))))),
     Post => Has_Failed = False;

   procedure Calculate_Negative_Target_For_Length_11_Case_2_147_483_63X (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range (Source'First + 9)..(Source'First + 10)) of Integer :=
        (3, 9) with Ghost;

      type Number_Array_Type is array (Integer range (Source'First + 9)..(Source'First + 10)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range (Source'First + 9)..(Source'First + 10) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in (Source'First + 9)..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in (Source'First + 9)..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := -N(Source'First + 10);
      pragma Assert (Target >= -9);

      Target := Target - N(Source'First + 9) *            10;
      pragma Assert (Target >= -39);

      Target := Target - 2_147_483_600;
      pragma Assert (Target >= -2_147_483_639);

      Has_Failed := False;
   end Calculate_Negative_Target_For_Length_11_Case_2_147_483_63X;

   procedure Calculate_Negative_Target_For_Length_11_Case_2_147_483_5XX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean) with
     Pre  => (Source'Length = 11 and then (Source(Source'First + 0) = '-' and
                Source(Source'First + 1) <= '2' and
                Source(Source'First + 2) = '1' and
                Source(Source'First + 3) = '4' and
                Source(Source'First + 4) = '7' and
                Source(Source'First + 5) = '4' and
                Source(Source'First + 6) = '8' and
                Source(Source'First + 7) = '3' and
                Source(Source'First + 8) < '6' and
                (for all Index in (Source'First + 8)..(Source'First + 10) => Aida.Characters.Is_Digit (Source (Index))))),
     Post => Has_Failed = False;

   procedure Calculate_Negative_Target_For_Length_11_Case_2_147_483_5XX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range (Source'First + 8)..(Source'First + 10)) of Integer :=
        (5, 9, 9) with Ghost;

      type Number_Array_Type is array (Integer range (Source'First + 8)..(Source'First + 10)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range (Source'First + 8)..(Source'First + 10) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in (Source'First + 8)..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in (Source'First + 8)..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := -N(Source'First + 10);
      pragma Assert (Target >= -9);

      Target := Target - N(Source'First + 9) *            10;
      pragma Assert (Target >= -99);

      Target := Target - N(Source'First + 8) *           100;
      pragma Assert (Target >= -599);

      Target := Target - 2_147_483_000;
      pragma Assert (Target >= -2_147_483_599);

      Has_Failed := False;
   end Calculate_Negative_Target_For_Length_11_Case_2_147_483_5XX;

   procedure Calculate_Negative_Target_For_Length_11_Case_2_147_482_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean) with
     Pre  => (Source'Length = 11 and then (Source(Source'First + 0) = '-' and
                Source(Source'First + 1) = '2' and
                Source(Source'First + 2) = '1' and
                Source(Source'First + 3) = '4' and
                Source(Source'First + 4) = '7' and
                Source(Source'First + 5) = '4' and
                Source(Source'First + 6) = '8' and
                Source(Source'First + 7) < '3' and
                (for all Index in (Source'First + 7)..(Source'First + 10) => Aida.Characters.Is_Digit (Source (Index))))),
     Post => Has_Failed = False;

   procedure Calculate_Negative_Target_For_Length_11_Case_2_147_482_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range (Source'First + 7)..(Source'First + 10)) of Integer :=
        (2, 9, 9, 9) with Ghost;

      type Number_Array_Type is array (Integer range (Source'First + 7)..(Source'First + 10)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range (Source'First + 7)..(Source'First + 10) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in (Source'First + 7)..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in (Source'First + 7)..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := -N(Source'First + 10);
      pragma Assert (Target >= -9);

      Target := Target - N(Source'First + 9) *            10;
      pragma Assert (Target >= -99);

      Target := Target - N(Source'First + 8) *           100;
      pragma Assert (Target >= -999);

      Target := Target - N(Source'First + 7) *         1_000;
      pragma Assert (Target >= -2_999);

      Target := Target - 2_147_480_000;
      pragma Assert (Target >= -2_147_482_999);

      Has_Failed := False;
   end Calculate_Negative_Target_For_Length_11_Case_2_147_482_XXX;

   procedure Calculate_Negative_Target_For_Length_11_Case_2_147_47X_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean) with
     Pre  => (Source'Length = 11 and then (Source(Source'First + 0) = '-' and
                Source(Source'First + 1) = '2' and
                Source(Source'First + 2) = '1' and
                Source(Source'First + 3) = '4' and
                Source(Source'First + 4) = '7' and
                Source(Source'First + 5) = '4' and
                Source(Source'First + 6) < '8' and
                (for all Index in (Source'First + 6)..(Source'First + 10) => Aida.Characters.Is_Digit (Source (Index))))),
     Post => Has_Failed = False;

   procedure Calculate_Negative_Target_For_Length_11_Case_2_147_47X_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range (Source'First + 6)..(Source'First + 10)) of Integer :=
        (7, 9, 9, 9, 9) with Ghost;

      type Number_Array_Type is array (Integer range (Source'First + 6)..(Source'First + 10)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range (Source'First + 6)..(Source'First + 10) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in (Source'First + 6)..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in (Source'First + 6)..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := -N(Source'First + 10);
      pragma Assert (Target >= -9);

      Target := Target - N(Source'First + 9) *            10;
      pragma Assert (Target >= -99);

      Target := Target - N(Source'First + 8) *           100;
      pragma Assert (Target >= -999);

      Target := Target - N(Source'First + 7) *         1_000;
      pragma Assert (Target >= -9_999);

      Target := Target - N(Source'First + 6) *        10_000;
      pragma Assert (Target >= -79_999);

      Target := Target - 2_147_400_000;
      pragma Assert (Target >= -2_147_479_999);

      Has_Failed := False;
   end Calculate_Negative_Target_For_Length_11_Case_2_147_47X_XXX;

   procedure Calculate_Negative_Target_For_Length_11_Case_2_147_3XX_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean) with
     Pre  => (Source'Length = 11 and then (Source(Source'First + 0) = '-' and
                Source(Source'First + 1) = '2' and
                Source(Source'First + 2) = '1' and
                Source(Source'First + 3) = '4' and
                Source(Source'First + 4) = '7' and
                Source(Source'First + 5) < '4' and
                (for all Index in (Source'First + 5)..(Source'First + 10) => Aida.Characters.Is_Digit (Source (Index))))),
     Post => Has_Failed = False;

   procedure Calculate_Negative_Target_For_Length_11_Case_2_147_3XX_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range (Source'First + 5)..(Source'First + 10)) of Integer :=
        (3, 9, 9, 9, 9, 9) with Ghost;

      type Number_Array_Type is array (Integer range (Source'First + 5)..(Source'First + 10)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range (Source'First + 5)..(Source'First + 10) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in (Source'First + 5)..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in (Source'First + 5)..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := -N(Source'First + 10);
      pragma Assert (Target >= -9);

      Target := Target - N(Source'First + 9) *            10;
      pragma Assert (Target >= -99);

      Target := Target - N(Source'First + 8) *           100;
      pragma Assert (Target >= -999);

      Target := Target - N(Source'First + 7) *         1_000;
      pragma Assert (Target >= -9_999);

      Target := Target - N(Source'First + 6) *        10_000;
      pragma Assert (Target >= -99_999);

      Target := Target - N(Source'First + 5) *       100_000;
      pragma Assert (Target >= -399_999);

      Target := Target - 2_147_000_000;
      pragma Assert (Target >= -2_147_399_999);

      Has_Failed := False;
   end Calculate_Negative_Target_For_Length_11_Case_2_147_3XX_XXX;

   procedure Calculate_Negative_Target_For_Length_11_Case_2_146_XXX_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean) with
     Pre  => (Source'Length = 11 and then (Source(Source'First + 0) = '-' and
                Source(Source'First + 1) = '2' and
                Source(Source'First + 2) = '1' and
                Source(Source'First + 3) = '4' and
                Source(Source'First + 4) < '7' and
                (for all Index in (Source'First + 4)..(Source'First + 10) => Aida.Characters.Is_Digit (Source (Index))))),
     Post => Has_Failed = False;

   procedure Calculate_Negative_Target_For_Length_11_Case_2_146_XXX_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range (Source'First + 4)..(Source'First + 10)) of Integer :=
        (6, 9, 9, 9, 9, 9, 9) with Ghost;

      type Number_Array_Type is array (Integer range (Source'First + 4)..(Source'First + 10)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range (Source'First + 4)..(Source'First + 10) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in (Source'First + 4)..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in (Source'First + 4)..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := -N(Source'First + 10);
      pragma Assert (Target >= -9);

      Target := Target - N(Source'First + 9) *            10;
      pragma Assert (Target >= -99);

      Target := Target - N(Source'First + 8) *           100;
      pragma Assert (Target >= -999);

      Target := Target - N(Source'First + 7) *         1_000;
      pragma Assert (Target >= -9_999);

      Target := Target - N(Source'First + 6) *        10_000;
      pragma Assert (Target >= -99_999);

      Target := Target - N(Source'First + 5) *       100_000;
      pragma Assert (Target >= -999_999);

      Target := Target - N(Source'First + 4) *     1_000_000;
      pragma Assert (Target >= -6_999_999);

      Target := Target - 2_140_000_000;
      pragma Assert (Target >= -2_146_999_999);

      Has_Failed := False;
   end Calculate_Negative_Target_For_Length_11_Case_2_146_XXX_XXX;

   procedure Calculate_Negative_Target_For_Length_11_Case_2_13X_XXX_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean) with
     Pre  => (Source'Length = 11 and then (Source(Source'First + 0) = '-' and
                Source(Source'First + 1) = '2' and
                Source(Source'First + 2) = '1' and
                Source(Source'First + 3) < '4' and
                (for all Index in (Source'First + 3)..(Source'First + 10) => Aida.Characters.Is_Digit (Source (Index))))),
     Post => Has_Failed = False;

   procedure Calculate_Negative_Target_For_Length_11_Case_2_13X_XXX_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range (Source'First + 3)..(Source'First + 10)) of Integer :=
        (3, 9, 9, 9, 9, 9, 9, 9) with Ghost;

      type Number_Array_Type is array (Integer range (Source'First + 3)..(Source'First + 10)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range (Source'First + 3)..(Source'First + 10) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in (Source'First + 3)..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in (Source'First + 3)..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := -N(Source'First + 10);
      pragma Assert (Target >= -9);

      Target := Target - N(Source'First + 9) *            10;
      pragma Assert (Target >= -99);

      Target := Target - N(Source'First + 8) *           100;
      pragma Assert (Target >= -999);

      Target := Target - N(Source'First + 7) *         1_000;
      pragma Assert (Target >= -9_999);

      Target := Target - N(Source'First + 6) *        10_000;
      pragma Assert (Target >= -99_999);

      Target := Target - N(Source'First + 5) *       100_000;
      pragma Assert (Target >= -999_999);

      Target := Target - N(Source'First + 4) *     1_000_000;
      pragma Assert (Target >= -9_999_999);

      Target := Target - N(Source'First + 3) *    10_000_000;
      pragma Assert (Target >= -39_999_999);

      Target := Target - 2_100_000_000;
      pragma Assert (Target >= -2_139_999_999);

      Has_Failed := False;
   end Calculate_Negative_Target_For_Length_11_Case_2_13X_XXX_XXX;

   procedure Calculate_Negative_Target_For_Length_11_Case_2_0XX_XXX_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean) with
     Pre  => (Source'Length = 11 and then (Source(Source'First + 0) = '-' and
                Source(Source'First + 1) = '2' and
                Source(Source'First + 2) = '0' and
                (for all Index in (Source'First + 2)..(Source'First + 10) => Aida.Characters.Is_Digit (Source (Index))))),
     Post => Has_Failed = False;

   procedure Calculate_Negative_Target_For_Length_11_Case_2_0XX_XXX_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range (Source'First + 2)..(Source'First + 10)) of Integer :=
        (0, 9, 9, 9, 9, 9, 9, 9, 9) with Ghost;

      type Number_Array_Type is array (Integer range (Source'First + 2)..(Source'First + 10)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range (Source'First + 2)..(Source'First + 10) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in (Source'First + 2)..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in (Source'First + 2)..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := -N(Source'First + 10);
      pragma Assert (Target >= -9);

      Target := Target - N(Source'First + 9) *            10;
      pragma Assert (Target >= -99);

      Target := Target - N(Source'First + 8) *           100;
      pragma Assert (Target >= -999);

      Target := Target - N(Source'First + 7) *         1_000;
      pragma Assert (Target >= -9_999);

      Target := Target - N(Source'First + 6) *        10_000;
      pragma Assert (Target >= -99_999);

      Target := Target - N(Source'First + 5) *       100_000;
      pragma Assert (Target >= -999_999);

      Target := Target - N(Source'First + 4) *     1_000_000;
      pragma Assert (Target >= -9_999_999);

      Target := Target - N(Source'First + 3) *    10_000_000;
      pragma Assert (Target >= -99_999_999);

      Target := Target - 2_000_000_000;
      pragma Assert (Target >= -2_099_999_999);

      Has_Failed := False;
   end Calculate_Negative_Target_For_Length_11_Case_2_0XX_XXX_XXX;

   procedure Calculate_Negative_Target_For_Length_11_Case_1_XXX_XXX_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean) with
     Pre  => (Source'Length = 11 and then (Source(Source'First + 0) = '-' and
                Source(Source'First + 1) < '2' and
                (for all Index in (Source'First + 1)..(Source'First + 10) => Aida.Characters.Is_Digit (Source (Index))))),
     Post => Has_Failed = False;

   procedure Calculate_Negative_Target_For_Length_11_Case_1_XXX_XXX_XXX (Source     : in  String;
                                                                         Target     : out Integer;
                                                                         Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range (Source'First + 1)..(Source'First + 10)) of Integer :=
        (1, 9, 9, 9, 9, 9, 9, 9, 9, 9) with Ghost;

      type Number_Array_Type is array (Integer range (Source'First + 1)..(Source'First + 10)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range (Source'First + 1)..(Source'First + 10) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in (Source'First + 1)..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in (Source'First + 1)..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := -N(Source'First + 10);
      pragma Assert (Target >= -9);

      Target := Target - N(Source'First + 9) *            10;
      pragma Assert (Target >= -99);

      Target := Target - N(Source'First + 8) *           100;
      pragma Assert (Target >= -999);

      Target := Target - N(Source'First + 7) *         1_000;
      pragma Assert (Target >= -9_999);

      Target := Target - N(Source'First + 6) *        10_000;
      pragma Assert (Target >= -99_999);

      Target := Target - N(Source'First + 5) *       100_000;
      pragma Assert (Target >= -999_999);

      Target := Target - N(Source'First + 4) *     1_000_000;
      pragma Assert (Target >= -9_999_999);

      Target := Target - N(Source'First + 3) *    10_000_000;
      pragma Assert (Target >= -99_999_999);

      Target := Target - N(Source'First + 2) *   100_000_000;
      pragma Assert (Target >= -999_999_999);

      Target := Target - 1_000_000_000;
      pragma Assert (Target >= -1_999_999_999);

      Has_Failed := False;
   end Calculate_Negative_Target_For_Length_11_Case_1_XXX_XXX_XXX;

   procedure Calculate_Negative_Target_Length_10 (Source     : in  String;
                                                  Target     : out Integer;
                                                  Has_Failed : out Boolean) with
     Pre  => (Source'Length = 10 and then (Source(Source'First + 0) = '-' and
                (for all Index in (Source'First + 1)..(Source'First + 9) => Aida.Characters.Is_Digit (Source (Index))))),
     Post => Has_Failed = False;

   procedure Calculate_Negative_Target_Length_10 (Source     : in  String;
                                                  Target     : out Integer;
                                                  Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range (Source'First + 1)..(Source'First + 9)) of Integer :=
        (9, 9, 9, 9, 9, 9, 9, 9, 9) with Ghost;

      type Number_Array_Type is array (Integer range (Source'First + 1)..(Source'First + 9)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range (Source'First + 1)..(Source'First + 9) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in (Source'First + 1)..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in (Source'First + 1)..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := -N(Source'First + 9);
      pragma Assert (Target >= -9);

      Target := Target - N(Source'First + 8) *            10;
      pragma Assert (Target >= -99);

      Target := Target - N(Source'First + 7) *           100;
      pragma Assert (Target >= -999);

      Target := Target - N(Source'First + 6) *         1_000;
      pragma Assert (Target >= -9_999);

      Target := Target - N(Source'First + 5) *        10_000;
      pragma Assert (Target >= -99_999);

      Target := Target - N(Source'First + 4) *       100_000;
      pragma Assert (Target >= -999_999);

      Target := Target - N(Source'First + 3) *     1_000_000;
      pragma Assert (Target >= -9_999_999);

      Target := Target - N(Source'First + 2) *    10_000_000;
      pragma Assert (Target >= -99_999_999);

      Target := Target - N(Source'First + 1) *   100_000_000;
      pragma Assert (Target >= -999_999_999);

      Has_Failed := False;
   end Calculate_Negative_Target_Length_10;

   procedure Calculate_Negative_Target_Length_9 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean) with
     Pre  => (Source'Length = 9 and then (Source(Source'First + 0) = '-' and
                (for all Index in (Source'First + 1)..(Source'First + 8) => Aida.Characters.Is_Digit (Source (Index))))),
     Post => Has_Failed = False;

   procedure Calculate_Negative_Target_Length_9 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range (Source'First + 1)..(Source'First + 8)) of Integer :=
        (9, 9, 9, 9, 9, 9, 9, 9) with Ghost;

      type Number_Array_Type is array (Integer range (Source'First + 1)..(Source'First + 8)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range (Source'First + 1)..(Source'First + 8) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in (Source'First + 1)..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in (Source'First + 1)..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := -N(Source'First + 8);
      pragma Assert (Target >= -9);

      Target := Target - N(Source'First + 7) *            10;
      pragma Assert (Target >= -99);

      Target := Target - N(Source'First + 6) *           100;
      pragma Assert (Target >= -999);

      Target := Target - N(Source'First + 5) *         1_000;
      pragma Assert (Target >= -9_999);

      Target := Target - N(Source'First + 4) *        10_000;
      pragma Assert (Target >= -99_999);

      Target := Target - N(Source'First + 3) *       100_000;
      pragma Assert (Target >= -999_999);

      Target := Target - N(Source'First + 2) *     1_000_000;
      pragma Assert (Target >= -9_999_999);

      Target := Target - N(Source'First + 1) *    10_000_000;
      pragma Assert (Target >= -99_999_999);

      Has_Failed := False;
   end Calculate_Negative_Target_Length_9;

   procedure Calculate_Negative_Target_Length_8 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean) with
     Pre  => (Source'Length = 8 and then (Source(Source'First + 0) = '-' and
                (for all Index in (Source'First + 1)..(Source'First + 7) => Aida.Characters.Is_Digit (Source (Index))))),
     Post => Has_Failed = False;

   procedure Calculate_Negative_Target_Length_8 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range (Source'First + 1)..(Source'First + 7)) of Integer :=
        (9, 9, 9, 9, 9, 9, 9) with Ghost;

      type Number_Array_Type is array (Integer range (Source'First + 1)..(Source'First + 7)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range (Source'First + 1)..(Source'First + 7) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in (Source'First + 1)..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in (Source'First + 1)..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := -N(Source'First + 7);
      pragma Assert (Target >= -9);

      Target := Target - N(Source'First + 6) *            10;
      pragma Assert (Target >= -99);

      Target := Target - N(Source'First + 5) *           100;
      pragma Assert (Target >= -999);

      Target := Target - N(Source'First + 4) *         1_000;
      pragma Assert (Target >= -9_999);

      Target := Target - N(Source'First + 3) *        10_000;
      pragma Assert (Target >= -99_999);

      Target := Target - N(Source'First + 2) *       100_000;
      pragma Assert (Target >= -999_999);

      Target := Target - N(Source'First + 1) *     1_000_000;
      pragma Assert (Target >= -9_999_999);

      Has_Failed := False;
   end Calculate_Negative_Target_Length_8;

   procedure Calculate_Negative_Target_Length_7 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean) with
     Pre  => (Source'Length = 7 and then (Source(Source'First + 0) = '-' and
                (for all Index in (Source'First + 1)..(Source'First + 6) => Aida.Characters.Is_Digit (Source (Index))))),
     Post => Has_Failed = False;

   procedure Calculate_Negative_Target_Length_7 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range (Source'First + 1)..(Source'First + 6)) of Integer :=
        (9, 9, 9, 9, 9, 9) with Ghost;

      type Number_Array_Type is array (Integer range (Source'First + 1)..(Source'First + 6)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range (Source'First + 1)..(Source'First + 6) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in (Source'First + 1)..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in (Source'First + 1)..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := -N(Source'First + 6);
      pragma Assert (Target >= -9);

      Target := Target - N(Source'First + 5) *            10;
      pragma Assert (Target >= -99);

      Target := Target - N(Source'First + 4) *           100;
      pragma Assert (Target >= -999);

      Target := Target - N(Source'First + 3) *         1_000;
      pragma Assert (Target >= -9_999);

      Target := Target - N(Source'First + 2) *        10_000;
      pragma Assert (Target >= -99_999);

      Target := Target - N(Source'First + 1) *       100_000;
      pragma Assert (Target >= -999_999);

      Has_Failed := False;
   end Calculate_Negative_Target_Length_7;

   procedure Calculate_Negative_Target_Length_6 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean) with
     Pre  => (Source'Length = 6 and then (Source(Source'First + 0) = '-' and
                (for all Index in (Source'First + 1)..(Source'First + 5) => Aida.Characters.Is_Digit (Source (Index))))),
     Post => Has_Failed = False;

   procedure Calculate_Negative_Target_Length_6 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range (Source'First + 1)..(Source'First + 5)) of Integer :=
        (9, 9, 9, 9, 9) with Ghost;

      type Number_Array_Type is array (Integer range (Source'First + 1)..(Source'First + 5)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range (Source'First + 1)..(Source'First + 5) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in (Source'First + 1)..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in (Source'First + 1)..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := -N(Source'First + 5);
      pragma Assert (Target >= -9);

      Target := Target - N(Source'First + 4) *            10;
      pragma Assert (Target >= -99);

      Target := Target - N(Source'First + 3) *           100;
      pragma Assert (Target >= -999);

      Target := Target - N(Source'First + 2) *         1_000;
      pragma Assert (Target >= -9_999);

      Target := Target - N(Source'First + 1) *        10_000;
      pragma Assert (Target >= -99_999);

      Has_Failed := False;
   end Calculate_Negative_Target_Length_6;

   procedure Calculate_Negative_Target_Length_5 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean) with
     Pre  => (Source'Length = 5 and then (Source(Source'First + 0) = '-' and
                (for all Index in (Source'First + 1)..(Source'First + 4) => Aida.Characters.Is_Digit (Source (Index))))),
     Post => Has_Failed = False;

   procedure Calculate_Negative_Target_Length_5 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range (Source'First + 1)..(Source'First + 4)) of Integer :=
        (9, 9, 9, 9) with Ghost;

      type Number_Array_Type is array (Integer range (Source'First + 1)..(Source'First + 4)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range (Source'First + 1)..(Source'First + 4) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in (Source'First + 1)..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in (Source'First + 1)..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := -N(Source'First + 4);
      pragma Assert (Target >= -9);

      Target := Target - N(Source'First + 3) *            10;
      pragma Assert (Target >= -99);

      Target := Target - N(Source'First + 2) *           100;
      pragma Assert (Target >= -999);

      Target := Target - N(Source'First + 1) *         1_000;
      pragma Assert (Target >= -9_999);

      Has_Failed := False;
   end Calculate_Negative_Target_Length_5;

   procedure Calculate_Negative_Target_Length_4 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean) with
     Pre  => (Source'Length = 4 and then (Source(Source'First + 0) = '-' and
                (for all Index in (Source'First + 1)..(Source'First + 3) => Aida.Characters.Is_Digit (Source (Index))))),
     Post => Has_Failed = False;

   procedure Calculate_Negative_Target_Length_4 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range (Source'First + 1)..(Source'First + 3)) of Integer :=
        (9, 9, 9) with Ghost;

      type Number_Array_Type is array (Integer range (Source'First + 1)..(Source'First + 3)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range (Source'First + 1)..(Source'First + 3) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in (Source'First + 1)..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in (Source'First + 1)..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := -N(Source'First + 3);
      pragma Assert (Target >= -9);

      Target := Target - N(Source'First + 2) *            10;
      pragma Assert (Target >= -99);

      Target := Target - N(Source'First + 1) *           100;
      pragma Assert (Target >= -999);

      Has_Failed := False;
   end Calculate_Negative_Target_Length_4;

   procedure Calculate_Negative_Target_Length_3 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean) with
     Pre  => (Source'Length = 3 and then (Source(Source'First + 0) = '-' and
                (for all Index in (Source'First + 1)..(Source'First + 2) => Aida.Characters.Is_Digit (Source (Index))))),
     Post => Has_Failed = False;

   procedure Calculate_Negative_Target_Length_3 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean)
   is
      Int_Array : array (Integer range (Source'First + 1)..(Source'First + 2)) of Integer :=
        (9, 9) with Ghost;

      type Number_Array_Type is array (Integer range (Source'First + 1)..(Source'First + 2)) of Integer;

      N : Number_Array_Type := (others => 0);
   begin
      for Index in Integer range (Source'First + 1)..(Source'First + 2) loop
         Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Index),
                                                             Target => N (Index));
         pragma Loop_Invariant (for all I in (Source'First + 1)..Index => 0 <= N(I) and N(I) <= 9);
         pragma Loop_Invariant (for all J in (Source'First + 1)..Index => N(J) <= Int_Array(J));
      end loop;

      pragma Assert (for all I in N'Range => 0 <= N(I) and N(I) <= Int_Array(I));

      Target := -N(Source'First + 2);
      pragma Assert (Target >= -9);

      Target := Target - N(Source'First + 1) *            10;
      pragma Assert (Target >= -99);

      Has_Failed := False;
   end Calculate_Negative_Target_Length_3;

   procedure Calculate_Negative_Target_Length_2 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean) with
     Pre  => (Source'Length = 2 and then (Source(Source'First + 0) = '-' and
                (for all Index in (Source'First + 1)..(Source'First + 1) => Aida.Characters.Is_Digit (Source (Index))))),
     Post => Has_Failed = False;

   procedure Calculate_Negative_Target_Length_2 (Source     : in  String;
                                                 Target     : out Integer;
                                                 Has_Failed : out Boolean) is
   begin
      Aida.Conversion.Convert_Character_Digit_To_Integer (Source => Source (Source'First + 1),
                                                          Target => Target);

      Target := -Target;

      pragma Assert (Target >= -9);

      Has_Failed := False;
   end Calculate_Negative_Target_Length_2;

   procedure Calculate_Negative_Target (Source     : in  String;
                                        Target     : out Integer;
                                        Has_Failed : out Boolean) with
     Pre            => (Source'Length <= 10 and (2 <= Source'Length and then ((Source (Source'First) = '-') and
                          (for all Index in Integer range (Source'First + 1) .. Source'Last => Aida.Characters.Is_Digit (Source (Index)))))),
     Post           => Has_Failed = False;

   procedure Calculate_Negative_Target (Source     : in  String;
                                        Target     : out Integer;
                                        Has_Failed : out Boolean) is
   begin
      case Source'Length is
         when 2 =>
            Calculate_Negative_Target_Length_2 (Source,
                                                Target,
                                                Has_Failed);
         when 3 =>
            Calculate_Negative_Target_Length_3 (Source,
                                                Target,
                                                Has_Failed);
         when 4 =>
            Calculate_Negative_Target_Length_4 (Source,
                                                Target,
                                                Has_Failed);
         when 5 =>
            Calculate_Negative_Target_Length_5 (Source,
                                                Target,
                                                Has_Failed);
         when 6 =>
            Calculate_Negative_Target_Length_6 (Source,
                                                Target,
                                                Has_Failed);
         when 7 =>
            Calculate_Negative_Target_Length_7 (Source,
                                                Target,
                                                Has_Failed);
         when 8 =>
            Calculate_Negative_Target_Length_8 (Source,
                                                Target,
                                                Has_Failed);
         when 9 =>
            Calculate_Negative_Target_Length_9 (Source,
                                                Target,
                                                Has_Failed);
         when 10 =>
            Calculate_Negative_Target_Length_10 (Source,
                                                 Target,
                                                 Has_Failed);
         when others =>
            Target := 0;
            Has_Failed := True;
      end case;
   end Calculate_Negative_Target;

   procedure Convert_String_To_Integer_Negative_Case (Source     : in  String;
                                                      Target     : out Integer;
                                                      Has_Failed : out Boolean) is
   begin
      Target := 0;

      if Source'Length = 11 then
         if Source (Source'First + 1) > '2' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 1) < '2' then
            Calculate_Negative_Target_For_Length_11_Case_1_XXX_XXX_XXX (Source,
                                                                        Target,
                                                                        Has_Failed);
            return;
         end if;

         if Source (Source'First + 2) > '1' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 2) < '1' then
            Calculate_Negative_Target_For_Length_11_Case_2_0XX_XXX_XXX (Source,
                                                                        Target,
                                                                        Has_Failed);
            return;
         end if;

         if Source (Source'First + 3) > '4' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 3) < '4' then
            Calculate_Negative_Target_For_Length_11_Case_2_13X_XXX_XXX (Source,
                                                                        Target,
                                                                        Has_Failed);
            return;
         end if;

         if Source (Source'First + 4) > '7' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 4) < '7' then
            Calculate_Negative_Target_For_Length_11_Case_2_146_XXX_XXX (Source,
                                                                        Target,
                                                                        Has_Failed);
            return;
         end if;

         if Source (Source'First + 5) > '4' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 5) < '4' then
            Calculate_Negative_Target_For_Length_11_Case_2_147_3XX_XXX (Source,
                                                                        Target,
                                                                        Has_Failed);
            return;
         end if;

         if Source (Source'First + 6) > '8' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 6) < '8' then
            Calculate_Negative_Target_For_Length_11_Case_2_147_47X_XXX (Source,
                                                                        Target,
                                                                        Has_Failed);
            return;
         end if;

         if Source (Source'First + 7) > '3' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 7) < '3' then
            Calculate_Negative_Target_For_Length_11_Case_2_147_482_XXX (Source,
                                                                        Target,
                                                                        Has_Failed);
            return;
         end if;

         if Source (Source'First + 8) > '6' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 8) < '6' then
            Calculate_Negative_Target_For_Length_11_Case_2_147_483_5XX (Source,
                                                                        Target,
                                                                        Has_Failed);
            return;
         end if;

         if Source (Source'First + 9) > '4' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 9) < '4' then
            Calculate_Negative_Target_For_Length_11_Case_2_147_483_63X (Source,
                                                                        Target,
                                                                        Has_Failed);
            return;
         end if;

         if Source (Source'First + 10) > '8' then
            Has_Failed := True;
            return;
         end if;

         Calculate_Negative_Target_For_Length_11_Case_2_147_483_648 (Source,
                                                                     Target,
                                                                     Has_Failed);
      else
         Calculate_Negative_Target (Source,
                                    Target,
                                    Has_Failed);
      end if;
   end Convert_String_To_Integer_Negative_Case;

end Aida.Conversion;
