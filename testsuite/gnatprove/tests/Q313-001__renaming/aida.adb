with Ada.Strings.Fixed;
with Ada.Text_IO;

package body Aida is
   pragma SPARK_Mode (On);

   use Aida.Character;

   package body String is

      use Aida.Character;

      function I (Source : T;
                  Index  : Natural) return Int32_T is
      begin
         return (Character.To_Int32 (Source (Source'First + Index)));
      end I;

      procedure Calculate_Positive_Target_For_Length_10_Case_2_147_483_647 (Source     : in  String_T;
                                                                            Target     : out Int32_T);
      pragma SPARK_Mode (On);
      pragma Precondition (Source'Length = 10 and then
                             ((for all Index in Source'Range => Character.Is_Digit (Source (Index))) and then
                                  (Source(Source'First + 0) = '2' and
                                         Source(Source'First + 1) = '1' and
                                         Source(Source'First + 2) = '4' and
                                         Source(Source'First + 3) = '7' and
                                         Source(Source'First + 4) = '4' and
                                         Source(Source'First + 5) = '8' and
                                         Source(Source'First + 6) = '3' and
                                         Source(Source'First + 7) = '6' and
                                         Source(Source'First + 8) = '4' and
                                         Source(Source'First + 9) < '8')));
      pragma Postcondition (Target = 2_147_483_640 + I (Source, 9));

      procedure Calculate_Positive_Target_For_Length_10_Case_2_147_483_647 (Source     : in  String_T;
                                                                            Target     : out Int32_T) is
      begin
         Target := 2_147_483_640 + To_Int32 (Source (Source'First + 9));
      end Calculate_Positive_Target_For_Length_10_Case_2_147_483_647;

      procedure Calculate_Positive_Target_For_Length_10_Case_2_147_483_63X (Source     : in  String_T;
                                                                            Target     : out Int32_T);
      pragma Precondition (Source'Length = 10 and then
                             ((for all Index in Source'Range => Character.Is_Digit (Source (Index))) and then
                                  (Source(Source'First + 0) = '2' and
                                         Source(Source'First + 1) = '1' and
                                         Source(Source'First + 2) = '4' and
                                         Source(Source'First + 3) = '7' and
                                         Source(Source'First + 4) = '4' and
                                         Source(Source'First + 5) = '8' and
                                         Source(Source'First + 6) = '3' and
                                         Source(Source'First + 7) = '6' and
                                         Source(Source'First + 8) < '4')));
      pragma Postcondition (Target = 2_147_483_600 + 10*I (Source, 8) + I (Source, 9));

      procedure Calculate_Positive_Target_For_Length_10_Case_2_147_483_63X (Source     : in  String_T;
                                                                            Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 8)..(Source'First + 9)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 8)..(Source'First + 9) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := N(Source'First + 9);
         Target := Target + N(Source'First + 8) *            10;
         Target := Target + 2_147_483_600;
      end Calculate_Positive_Target_For_Length_10_Case_2_147_483_63X;

      procedure Calculate_Positive_Target_For_Length_10_Case_2_147_483_5XX (Source     : in  String_T;
                                                                            Target     : out Int32_T);
      pragma Precondition (Source'Length = 10 and then
                             (for all Index in Source'Range => Character.Is_Digit (Source (Index)) and then
                                (Source(Source'First + 0) <= '2' and
                                     Source(Source'First + 1) = '1' and
                                     Source(Source'First + 2) = '4' and
                                     Source(Source'First + 3) = '7' and
                                     Source(Source'First + 4) = '4' and
                                     Source(Source'First + 5) = '8' and
                                     Source(Source'First + 6) = '3' and
                                     Source(Source'First + 7) < '6')));
      pragma Postcondition (Target = 2_147_483_000 + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9));

      procedure Calculate_Positive_Target_For_Length_10_Case_2_147_483_5XX (Source     : in  String_T;
                                                                            Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 7)..(Source'First + 9)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 7)..(Source'First + 9) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := N(Source'First + 9);
         Target := Target + N(Source'First + 8) *            10;
         Target := Target + N(Source'First + 7) *           100;
         Target := Target + 2_147_483_000;
      end Calculate_Positive_Target_For_Length_10_Case_2_147_483_5XX;

      procedure Calculate_Positive_Target_For_Length_10_Case_2_147_482_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T);
      pragma Precondition (Source'Length = 10 and then
                             (for all Index in Source'Range => Character.Is_Digit (Source (Index)) and then
                                (Source(Source'First + 0) = '2' and
                                     Source(Source'First + 1) = '1' and
                                     Source(Source'First + 2) = '4' and
                                     Source(Source'First + 3) = '7' and
                                     Source(Source'First + 4) = '4' and
                                     Source(Source'First + 5) = '8' and
                                     Source(Source'First + 6) < '3')));
      pragma Postcondition (Target = 2_147_480_000 + 1_000*I (Source, 6) + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9));

      procedure Calculate_Positive_Target_For_Length_10_Case_2_147_482_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 6)..(Source'First + 9)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 6)..(Source'First + 9) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := N(Source'First + 9);
         Target := Target + N(Source'First + 8) *            10;
         Target := Target + N(Source'First + 7) *           100;
         Target := Target + N(Source'First + 6) *         1_000;
         Target := Target + 2_147_480_000;
      end Calculate_Positive_Target_For_Length_10_Case_2_147_482_XXX;

      procedure Calculate_Positive_Target_For_Length_10_Case_2_147_47X_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T);
      pragma Precondition ((Source'Length = 10 and then
                             (for all Index in Source'Range => Character.Is_Digit (Source (Index)) and then
                                (Source(Source'First + 0) = '2' and
                                     Source(Source'First + 1) = '1' and
                                     Source(Source'First + 2) = '4' and
                                     Source(Source'First + 3) = '7' and
                                     Source(Source'First + 4) = '4' and
                                     Source(Source'First + 5) < '8'))));
      pragma Postcondition (Target = 2_147_400_000 + 10_000*I (Source, 5) + 1_000*I (Source, 6) + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9));

      procedure Calculate_Positive_Target_For_Length_10_Case_2_147_47X_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 5)..(Source'First + 9)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 5)..(Source'First + 9) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := N(Source'First + 9);
         Target := Target + N(Source'First + 8) *            10;
         Target := Target + N(Source'First + 7) *           100;
         Target := Target + N(Source'First + 6) *         1_000;
         Target := Target + N(Source'First + 5) *        10_000;
         Target := Target + 2_147_400_000;
      end Calculate_Positive_Target_For_Length_10_Case_2_147_47X_XXX;

      procedure Calculate_Positive_Target_For_Length_10_Case_2_147_3XX_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T);
      pragma Precondition ((Source'Length = 10 and then
                             (for all Index in Source'Range => Character.Is_Digit (Source (Index)) and then
                                (Source(Source'First + 0) = '2' and
                                     Source(Source'First + 1) = '1' and
                                     Source(Source'First + 2) = '4' and
                                     Source(Source'First + 3) = '7' and
                                     Source(Source'First + 4) < '4'))));
      pragma Postcondition (Target = 2_147_000_000 + 100_000*I (Source, 4) + 10_000*I (Source, 5) + 1_000*I (Source, 6) + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9));

      procedure Calculate_Positive_Target_For_Length_10_Case_2_147_3XX_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 4)..(Source'First + 9)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 4)..(Source'First + 9) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := N(Source'First + 9);
         Target := Target + N(Source'First + 8) *            10;
         Target := Target + N(Source'First + 7) *           100;
         Target := Target + N(Source'First + 6) *         1_000;
         Target := Target + N(Source'First + 5) *        10_000;
         Target := Target + N(Source'First + 4) *       100_000;
         Target := Target + 2_147_000_000;
      end Calculate_Positive_Target_For_Length_10_Case_2_147_3XX_XXX;

      procedure Calculate_Positive_Target_For_Length_10_Case_2_146_XXX_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T);
      pragma Precondition ((Source'Length = 10 and then
                             (for all Index in Source'Range => Character.Is_Digit (Source (Index)) and then
                                (Source(Source'First + 0) = '2' and
                                     Source(Source'First + 1) = '1' and
                                     Source(Source'First + 2) = '4' and
                                     Source(Source'First + 3) < '7'))));
      pragma Postcondition (Target = 2_140_000_000 + 1_000_000*I (Source, 3) + 100_000*I (Source, 4) + 10_000*I (Source, 5) + 1_000*I (Source, 6) + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9));

      procedure Calculate_Positive_Target_For_Length_10_Case_2_146_XXX_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 3)..(Source'First + 9)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 3)..(Source'First + 9) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := N(Source'First + 9);
         Target := Target + N(Source'First + 8) *            10;
         Target := Target + N(Source'First + 7) *           100;
         Target := Target + N(Source'First + 6) *         1_000;
         Target := Target + N(Source'First + 5) *        10_000;
         Target := Target + N(Source'First + 4) *       100_000;
         Target := Target + N(Source'First + 3) *     1_000_000;
         Target := Target + 2_140_000_000;
      end Calculate_Positive_Target_For_Length_10_Case_2_146_XXX_XXX;

      procedure Calculate_Positive_Target_For_Length_10_Case_2_13X_XXX_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T);
      pragma Precondition ((Source'Length = 10 and then
                             (for all Index in Source'Range => Character.Is_Digit (Source (Index)) and then
                                (Source(Source'First + 0) = '2' and
                                     Source(Source'First + 1) = '1' and
                                     Source(Source'First + 2) < '4'))));
      pragma Postcondition (Target = 2_100_000_000 + 10_000_000*I (Source, 2) + 1_000_000*I (Source, 3) + 100_000*I (Source, 4) + 10_000*I (Source, 5) + 1_000*I (Source, 6) + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9));

      procedure Calculate_Positive_Target_For_Length_10_Case_2_13X_XXX_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 2)..(Source'First + 9)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 2)..(Source'First + 9) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := N(Source'First + 9);
         Target := Target + N(Source'First + 8) *            10;
         Target := Target + N(Source'First + 7) *           100;
         Target := Target + N(Source'First + 6) *         1_000;
         Target := Target + N(Source'First + 5) *        10_000;
         Target := Target + N(Source'First + 4) *       100_000;
         Target := Target + N(Source'First + 3) *     1_000_000;
         Target := Target + N(Source'First + 2) *    10_000_000;
         Target := Target + 2_100_000_000;
      end Calculate_Positive_Target_For_Length_10_Case_2_13X_XXX_XXX;

      procedure Calculate_Positive_Target_For_Length_10_Case_2_0XX_XXX_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T);
      pragma Precondition ((Source'Length = 10 and then
                             (for all Index in Source'Range => Character.Is_Digit (Source (Index)) and then
                                (Source(Source'First + 0) = '2' and
                                     Source(Source'First + 1) = '0'))));
      pragma Postcondition (Target = 2_000_000_000 + 10_000_000*I (Source, 2) + 1_000_000*I (Source, 3) + 100_000*I (Source, 4) + 10_000*I (Source, 5) + 1_000*I (Source, 6) + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9));

      procedure Calculate_Positive_Target_For_Length_10_Case_2_0XX_XXX_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 2)..(Source'First + 9)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 2)..(Source'First + 9) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := N(Source'First + 9);
         Target := Target + N(Source'First + 8) *            10;
         Target := Target + N(Source'First + 7) *           100;
         Target := Target + N(Source'First + 6) *         1_000;
         Target := Target + N(Source'First + 5) *        10_000;
         Target := Target + N(Source'First + 4) *       100_000;
         Target := Target + N(Source'First + 3) *     1_000_000;
         Target := Target + N(Source'First + 2) *    10_000_000;
         Target := Target + 2_000_000_000;
      end Calculate_Positive_Target_For_Length_10_Case_2_0XX_XXX_XXX;

      procedure Calculate_Positive_Target_For_Length_10_Case_1_XXX_XXX_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T);
      pragma Precondition ((Source'Length = 10 and then
                             (for all Index in Source'Range => Character.Is_Digit (Source (Index)) and then
                                (Source(Source'First + 0) < '2'))));
      pragma Postcondition (Target = 1_000_000_000*I (Source, 0) + 100_000_000*I (Source, 1) + 10_000_000*I (Source, 2) + 1_000_000*I (Source, 3) + 100_000*I (Source, 4) + 10_000*I (Source, 5) + 1_000*I (Source, 6) + 100*I (Source, 7) + 10*I (Source, 8) + I (Source, 9));

      procedure Calculate_Positive_Target_For_Length_10_Case_1_XXX_XXX_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range Source'First..(Source'First + 9)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range Source'First..(Source'First + 9) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := N(Source'First + 9);
         Target := Target + N(Source'First + 8) *            10;
         Target := Target + N(Source'First + 7) *           100;
         Target := Target + N(Source'First + 6) *         1_000;
         Target := Target + N(Source'First + 5) *        10_000;
         Target := Target + N(Source'First + 4) *       100_000;
         Target := Target + N(Source'First + 3) *     1_000_000;
         Target := Target + N(Source'First + 2) *    10_000_000;
         Target := Target + N(Source'First + 1) *   100_000_000;
         Target := Target + N(Source'First + 0) * 1_000_000_000;
      end Calculate_Positive_Target_For_Length_10_Case_1_XXX_XXX_XXX;

      procedure Calculate_Positive_Target_Length_9 (Source     : in  String_T;
                                                    Target     : out Int32_T);
      pragma Precondition (Source'Length = 9 and (for all Index in Source'Range => Character.Is_Digit (Source (Index))));
      pragma Postcondition (Target = I (Source, 0) * 100_000_000 +
                              I (Source, 1) * 10_000_000 +
                              I (Source, 2) * 1_000_000 +
                              I (Source, 3) * 100_000 +
                              I (Source, 4) * 10_000 +
                              I (Source, 5) * 1_000 +
                              I (Source, 6) * 100 +
                              I (Source, 7) * 10 +
                              I (Source, 8) * 1);

      procedure Calculate_Positive_Target_Length_9 (Source     : in  String_T;
                                                    Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range Source'First..(Source'First + 8)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range Source'First..(Source'First + 8) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := N(Source'First + 8);
         Target := Target + N(Source'First + 7) *            10;
         Target := Target + N(Source'First + 6) *           100;
         Target := Target + N(Source'First + 5) *         1_000;
         Target := Target + N(Source'First + 4) *        10_000;
         Target := Target + N(Source'First + 3) *       100_000;
         Target := Target + N(Source'First + 2) *     1_000_000;
         Target := Target + N(Source'First + 1) *    10_000_000;
         Target := Target + N(Source'First + 0) *   100_000_000;
      end Calculate_Positive_Target_Length_9;

      procedure Calculate_Positive_Target_Length_8 (Source     : in  String_T;
                                                    Target     : out Int32_T);
      pragma Precondition (Source'Length = 8 and (for all Index in Source'Range => Character.Is_Digit (Source (Index))));
      pragma Postcondition (Target =
                              I (Source, 0) * 10_000_000 +
                              I (Source, 1) * 1_000_000 +
                              I (Source, 2) * 100_000 +
                              I (Source, 3) * 10_000 +
                              I (Source, 4) * 1_000 +
                              I (Source, 5) * 100 +
                              I (Source, 6) * 10 +
                              I (Source, 7) * 1);

      procedure Calculate_Positive_Target_Length_8 (Source     : in  String_T;
                                                    Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range Source'First..(Source'First + 7)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range Source'First..(Source'First + 7) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := N(Source'First + 7);
         Target := Target + N(Source'First + 6) *            10;
         Target := Target + N(Source'First + 5) *           100;
         Target := Target + N(Source'First + 4) *         1_000;
         Target := Target + N(Source'First + 3) *        10_000;
         Target := Target + N(Source'First + 2) *       100_000;
         Target := Target + N(Source'First + 1) *     1_000_000;
         Target := Target + N(Source'First + 0) *    10_000_000;
      end Calculate_Positive_Target_Length_8;

      procedure Calculate_Positive_Target_Length_7 (Source     : in  String_T;
                                                    Target     : out Int32_T);
      pragma Precondition (Source'Length = 7 and (for all Index in Source'Range => Character.Is_Digit (Source (Index))));
      pragma Postcondition (Target = I (Source, 0) * 1_000_000 +
                              I (Source, 1) * 100_000 +
                              I (Source, 2) * 10_000 +
                              I (Source, 3) * 1_000 +
                              I (Source, 4) * 100 +
                              I (Source, 5) * 10 +
                              I (Source, 6) * 1);

      procedure Calculate_Positive_Target_Length_7 (Source     : in  String_T;
                                                    Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range Source'First..(Source'First + 6)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range Source'First..(Source'First + 6) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := N(Source'First + 6);
         Target := Target + N(Source'First + 5) *            10;
         Target := Target + N(Source'First + 4) *           100;
         Target := Target + N(Source'First + 3) *         1_000;
         Target := Target + N(Source'First + 2) *        10_000;
         Target := Target + N(Source'First + 1) *       100_000;
         Target := Target + N(Source'First + 0) *     1_000_000;
      end Calculate_Positive_Target_Length_7;

      procedure Calculate_Positive_Target_Length_6 (Source     : in  String_T;
                                                    Target     : out Int32_T);
      pragma Precondition (Source'Length = 6 and (for all Index in Source'Range => Character.Is_Digit (Source (Index))));
      pragma Postcondition (Target =
                              I (Source, 0) * 100_000 +
                              I (Source, 1) * 10_000 +
                              I (Source, 2) * 1_000 +
                              I (Source, 3) * 100 +
                              I (Source, 4) * 10 +
                              I (Source, 5) * 1);

      procedure Calculate_Positive_Target_Length_6 (Source     : in  String_T;
                                                    Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range Source'First..(Source'First + 5)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range Source'First..(Source'First + 5) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := N(Source'First + 5);
         Target := Target + N(Source'First + 4) *            10;
         Target := Target + N(Source'First + 3) *           100;
         Target := Target + N(Source'First + 2) *         1_000;
         Target := Target + N(Source'First + 1) *        10_000;
         Target := Target + N(Source'First + 0) *       100_000;
      end Calculate_Positive_Target_Length_6;

      procedure Calculate_Positive_Target_Length_5 (Source     : in  String_T;
                                                    Target     : out Int32_T);
      pragma Precondition (Source'Length = 5 and (for all Index in Source'Range => Character.Is_Digit (Source (Index))));
      pragma Postcondition (Target =
                              I (Source, 0) * 10_000 +
                              I (Source, 1) * 1_000 +
                              I (Source, 2) * 100 +
                              I (Source, 3) * 10 +
                              I (Source, 4) * 1);

      procedure Calculate_Positive_Target_Length_5 (Source     : in  String_T;
                                                    Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range Source'First..(Source'First + 4)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range Source'First..(Source'First + 4) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := N(Source'First + 4);
         Target := Target + N(Source'First + 3) *            10;
         Target := Target + N(Source'First + 2) *           100;
         Target := Target + N(Source'First + 1) *         1_000;
         Target := Target + N(Source'First + 0) *        10_000;
      end Calculate_Positive_Target_Length_5;

      procedure Calculate_Positive_Target_Length_4 (Source     : in  String_T;
                                                    Target     : out Int32_T);
      pragma Precondition (Source'Length = 4 and (for all Index in Source'Range => Character.Is_Digit (Source (Index))));
      pragma Postcondition (Target =
                              I (Source, 0) * 1_000 +
                              I (Source, 1) * 100 +
                              I (Source, 2) * 10 +
                              I (Source, 3) * 1);

      procedure Calculate_Positive_Target_Length_4 (Source     : in  String_T;
                                                    Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range Source'First..(Source'First + 3)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range Source'First..(Source'First + 3) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := N(Source'First + 3);
         Target := Target + N(Source'First + 2) *            10;
         Target := Target + N(Source'First + 1) *           100;
         Target := Target + N(Source'First + 0) *         1_000;
      end Calculate_Positive_Target_Length_4;

      procedure Calculate_Positive_Target_Length_3 (Source     : in  String_T;
                                                    Target     : out Int32_T);
      pragma Precondition (Source'Length = 3 and (for all Index in Source'Range => Character.Is_Digit (Source (Index))));
      pragma Postcondition (Target =
                              I (Source, 0) * 100 +
                              I (Source, 1) * 10 +
                              I (Source, 2) * 1);

      procedure Calculate_Positive_Target_Length_3 (Source     : in  String_T;
                                                    Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range Source'First..(Source'First + 2)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range Source'First..(Source'First + 2) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := N(Source'First + 2);
         Target := Target + N(Source'First + 1) *            10;
         Target := Target + N(Source'First + 0) *           100;
      end Calculate_Positive_Target_Length_3;

      procedure Calculate_Positive_Target_Length_2 (Source     : in  String_T;
                                                    Target     : out Int32_T);
      pragma Precondition (Source'Length = 2 and (for all Index in Source'Range => Character.Is_Digit (Source (Index))));
      pragma Postcondition (Target = I (Source, 0) * 10 + I (Source, 1));
      pragma Depends (Target => Source);

      procedure Calculate_Positive_Target_Length_2 (Source     : in  String_T;
                                                    Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range Source'First..(Source'First + 1)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range Source'First..(Source'First + 1) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := N(Source'First + 1);
         Target := Target + N(Source'First + 0) * 10;
      end Calculate_Positive_Target_Length_2;

      procedure Calculate_Positive_Target_Length_1 (Source     : in  String_T;
                                                    Target     : out Int32_T);
      pragma Precondition (Source'Length = 1 and (for all Index in Source'Range => Character.Is_Digit (Source (Index))));
      pragma Postcondition (Target = I (Source, 0));

      procedure Calculate_Positive_Target_Length_1 (Source     : in  String_T;
                                                    Target     : out Int32_T) is
      begin
         To_Int32 (Source => Source (Source'First),
                   Target => Target);
      end Calculate_Positive_Target_Length_1;

      procedure Calculate_Negative_Target_For_Length_11_Case_2_147_483_648 (Source     : in  String_T;
                                                                            Target     : out Int32_T);
      pragma Precondition ((Source'Length = 11 and then (Source(Source'First + 0) = '-' and
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
                             (for all Index in (Source'First + 10)..(Source'First + 10) => Character.Is_Digit (Source (Index))))));
      pragma Postcondition (Target = -2_147_483_640 - I (Source, 10));

      procedure Calculate_Negative_Target_For_Length_11_Case_2_147_483_648 (Source     : in  String_T;
                                                                            Target     : out Int32_T)
      is
         N : Int32_T;
      begin
         To_Int32 (Source => Source(Source'First + 10),
                   Target => N);

         Target := -N;
         Target := Target - 2_147_483_640;
      end Calculate_Negative_Target_For_Length_11_Case_2_147_483_648;

      procedure Calculate_Negative_Target_For_Length_11_Case_2_147_483_63X (Source     : in  String_T;
                                                                            Target     : out Int32_T);
      pragma Precondition (Source'Length = 11 and then (Source(Source'First + 0) = '-' and
                             Source(Source'First + 1) = '2' and
                             Source(Source'First + 2) = '1' and
                             Source(Source'First + 3) = '4' and
                             Source(Source'First + 4) = '7' and
                             Source(Source'First + 5) = '4' and
                             Source(Source'First + 6) = '8' and
                             Source(Source'First + 7) = '3' and
                             Source(Source'First + 8) = '6' and
                             Source(Source'First + 9) < '4' and
                             (for all Index in (Source'First + 9)..(Source'First + 10) => Character.Is_Digit (Source (Index)))));
      pragma Postcondition (Target = -2_147_483_600 -
                              10*I (Source, 9) - I (Source, 10));

      procedure Calculate_Negative_Target_For_Length_11_Case_2_147_483_63X (Source     : in  String_T;
                                                                            Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 9)..(Source'First + 10)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 9)..(Source'First + 10) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := -N(Source'First + 10);
         Target := Target - N(Source'First + 9) *            10;
         Target := Target - 2_147_483_600;
      end Calculate_Negative_Target_For_Length_11_Case_2_147_483_63X;

      procedure Calculate_Negative_Target_For_Length_11_Case_2_147_483_5XX (Source     : in  String_T;
                                                                            Target     : out Int32_T);
      pragma Precondition (Source'Length = 11 and then (Source(Source'First + 0) = '-' and
                             Source(Source'First + 1) <= '2' and
                             Source(Source'First + 2) = '1' and
                             Source(Source'First + 3) = '4' and
                             Source(Source'First + 4) = '7' and
                             Source(Source'First + 5) = '4' and
                             Source(Source'First + 6) = '8' and
                             Source(Source'First + 7) = '3' and
                             Source(Source'First + 8) < '6' and
                             (for all Index in (Source'First + 8)..(Source'First + 10) => Character.Is_Digit (Source (Index)))));
      pragma Postcondition (Target = -2_147_483_000 - 100*I (Source, 8) -
                              10*I (Source, 9) - I (Source, 10));

      procedure Calculate_Negative_Target_For_Length_11_Case_2_147_483_5XX (Source     : in  String_T;
                                                                            Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 8)..(Source'First + 10)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 8)..(Source'First + 10) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := -N(Source'First + 10);
         Target := Target - N(Source'First + 9) *            10;
         Target := Target - N(Source'First + 8) *           100;
         Target := Target - 2_147_483_000;
      end Calculate_Negative_Target_For_Length_11_Case_2_147_483_5XX;

      procedure Calculate_Negative_Target_For_Length_11_Case_2_147_482_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T);
      pragma Precondition (Source'Length = 11 and then (Source(Source'First + 0) = '-' and
                             Source(Source'First + 1) = '2' and
                             Source(Source'First + 2) = '1' and
                             Source(Source'First + 3) = '4' and
                             Source(Source'First + 4) = '7' and
                             Source(Source'First + 5) = '4' and
                             Source(Source'First + 6) = '8' and
                             Source(Source'First + 7) < '3' and
                             (for all Index in (Source'First + 7)..(Source'First + 10) => Character.Is_Digit (Source (Index)))));
      pragma Postcondition (Target = -2_147_480_000 - 1_000*I (Source, 7) -
                              100*I (Source, 8) -
                              10*I (Source, 9) - I (Source, 10));

      procedure Calculate_Negative_Target_For_Length_11_Case_2_147_482_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 7)..(Source'First + 10)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 7)..(Source'First + 10) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := -N(Source'First + 10);
         Target := Target - N(Source'First + 9) *            10;
         Target := Target - N(Source'First + 8) *           100;
         Target := Target - N(Source'First + 7) *         1_000;
         Target := Target - 2_147_480_000;
      end Calculate_Negative_Target_For_Length_11_Case_2_147_482_XXX;

      procedure Calculate_Negative_Target_For_Length_11_Case_2_147_47X_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T);
      pragma Precondition (Source'Length = 11 and then (Source(Source'First + 0) = '-' and
                             Source(Source'First + 1) = '2' and
                             Source(Source'First + 2) = '1' and
                             Source(Source'First + 3) = '4' and
                             Source(Source'First + 4) = '7' and
                             Source(Source'First + 5) = '4' and
                             Source(Source'First + 6) < '8' and
                             (for all Index in (Source'First + 6)..(Source'First + 10) => Character.Is_Digit (Source (Index)))));
      pragma Postcondition (Target = -2_147_400_000 - 10_000*I (Source, 6)-
                              1_000*I (Source, 7) - 100*I (Source, 8) -
                              10*I (Source, 9) - I (Source, 10));

      procedure Calculate_Negative_Target_For_Length_11_Case_2_147_47X_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 6)..(Source'First + 10)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 6)..(Source'First + 10) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := -N(Source'First + 10);
         Target := Target - N(Source'First + 9) *            10;
         Target := Target - N(Source'First + 8) *           100;
         Target := Target - N(Source'First + 7) *         1_000;
         Target := Target - N(Source'First + 6) *        10_000;
         Target := Target - 2_147_400_000;
      end Calculate_Negative_Target_For_Length_11_Case_2_147_47X_XXX;

      procedure Calculate_Negative_Target_For_Length_11_Case_2_147_3XX_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T);
      pragma Precondition (Source'Length = 11 and then (Source(Source'First + 0) = '-' and
                             Source(Source'First + 1) = '2' and
                             Source(Source'First + 2) = '1' and
                             Source(Source'First + 3) = '4' and
                             Source(Source'First + 4) = '7' and
                             Source(Source'First + 5) < '4' and
                             (for all Index in (Source'First + 5)..(Source'First + 10) => Character.Is_Digit (Source (Index)))));
      pragma Postcondition (Target = -2_147_000_000 - 100_000*I (Source, 5) -
                              10_000*I (Source, 6) -
                              1_000*I (Source, 7) - 100*I (Source, 8) -
                              10*I (Source, 9) - I (Source, 10));

      procedure Calculate_Negative_Target_For_Length_11_Case_2_147_3XX_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 5)..(Source'First + 10)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 5)..(Source'First + 10) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := -N(Source'First + 10);
         Target := Target - N(Source'First + 9) *            10;
         Target := Target - N(Source'First + 8) *           100;
         Target := Target - N(Source'First + 7) *         1_000;
         Target := Target - N(Source'First + 6) *        10_000;
         Target := Target - N(Source'First + 5) *       100_000;
         Target := Target - 2_147_000_000;
      end Calculate_Negative_Target_For_Length_11_Case_2_147_3XX_XXX;

      procedure Calculate_Negative_Target_For_Length_11_Case_2_146_XXX_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T);
      pragma Precondition (Source'Length = 11 and then (Source(Source'First + 0) = '-' and
                             Source(Source'First + 1) = '2' and
                             Source(Source'First + 2) = '1' and
                             Source(Source'First + 3) = '4' and
                             Source(Source'First + 4) < '7' and
                             (for all Index in (Source'First + 4)..(Source'First + 10) => Character.Is_Digit (Source (Index)))));
      pragma Postcondition (Target = -2_140_000_000 - 1_000_000*I (Source, 4) -
                              100_000*I (Source, 5) - 10_000*I (Source, 6) -
                              1_000*I (Source, 7) - 100*I (Source, 8) -
                              10*I (Source, 9) - I (Source, 10));

      procedure Calculate_Negative_Target_For_Length_11_Case_2_146_XXX_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 4)..(Source'First + 10)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 4)..(Source'First + 10) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := -N(Source'First + 10);
         Target := Target - N(Source'First + 9) *            10;
         Target := Target - N(Source'First + 8) *           100;
         Target := Target - N(Source'First + 7) *         1_000;
         Target := Target - N(Source'First + 6) *        10_000;
         Target := Target - N(Source'First + 5) *       100_000;
         Target := Target - N(Source'First + 4) *     1_000_000;
         Target := Target - 2_140_000_000;
      end Calculate_Negative_Target_For_Length_11_Case_2_146_XXX_XXX;

      procedure Calculate_Negative_Target_For_Length_11_Case_2_13X_XXX_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T);
      pragma Precondition (Source'Length = 11 and then (Source(Source'First + 0) = '-' and
                             Source(Source'First + 1) = '2' and
                             Source(Source'First + 2) = '1' and
                             Source(Source'First + 3) < '4' and
                             (for all Index in (Source'First + 3)..(Source'First + 10) => Character.Is_Digit (Source (Index)))));
      pragma Postcondition (Target = -2_100_000_000 - 10_000_000*I (Source, 3) -
                              1_000_000*I (Source, 4) -
                              100_000*I (Source, 5) - 10_000*I (Source, 6) -
                              1_000*I (Source, 7) - 100*I (Source, 8) -
                              10*I (Source, 9) - I (Source, 10));

      procedure Calculate_Negative_Target_For_Length_11_Case_2_13X_XXX_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 3)..(Source'First + 10)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 3)..(Source'First + 10) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := -N(Source'First + 10);
         Target := Target - N(Source'First + 9) *            10;
         Target := Target - N(Source'First + 8) *           100;
         Target := Target - N(Source'First + 7) *         1_000;
         Target := Target - N(Source'First + 6) *        10_000;
         Target := Target - N(Source'First + 5) *       100_000;
         Target := Target - N(Source'First + 4) *     1_000_000;
         Target := Target - N(Source'First + 3) *    10_000_000;
         Target := Target - 2_100_000_000;
      end Calculate_Negative_Target_For_Length_11_Case_2_13X_XXX_XXX;

      procedure Calculate_Negative_Target_For_Length_11_Case_2_0XX_XXX_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T);
      pragma Precondition (Source'Length = 11 and then (Source(Source'First + 0) = '-' and
                             Source(Source'First + 1) = '2' and
                             Source(Source'First + 2) = '0' and
                             (for all Index in (Source'First + 2)..(Source'First + 10) => Character.Is_Digit (Source (Index)))));
      pragma Postcondition (Target = -2_000_000_000 -
                              10_000_000*I (Source, 3) -
                              1_000_000*I (Source, 4) -
                              100_000*I (Source, 5) - 10_000*I (Source, 6) -
                              1_000*I (Source, 7) - 100*I (Source, 8) -
                              10*I (Source, 9) - I (Source, 10));

      procedure Calculate_Negative_Target_For_Length_11_Case_2_0XX_XXX_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 2)..(Source'First + 10)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 2)..(Source'First + 10) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := -N(Source'First + 10);
         Target := Target - N(Source'First + 9) *            10;
         Target := Target - N(Source'First + 8) *           100;
         Target := Target - N(Source'First + 7) *         1_000;
         Target := Target - N(Source'First + 6) *        10_000;
         Target := Target - N(Source'First + 5) *       100_000;
         Target := Target - N(Source'First + 4) *     1_000_000;
         Target := Target - N(Source'First + 3) *    10_000_000;
         Target := Target - 2_000_000_000;
      end Calculate_Negative_Target_For_Length_11_Case_2_0XX_XXX_XXX;

      procedure Calculate_Negative_Target_For_Length_11_Case_1_XXX_XXX_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T);
      pragma Precondition (Source'Length = 11 and then (Source(Source'First + 0) = '-' and
                             Source(Source'First + 1) < '2' and
                             (for all Index in (Source'First + 1)..(Source'First + 10) => Character.Is_Digit (Source (Index)))));
      pragma Postcondition (Target = -1_000_000_000*I (Source, 1) - 100_000_000*I (Source, 2) -
                              10_000_000*I (Source, 3) -
                              1_000_000*I (Source, 4) -
                              100_000*I (Source, 5) - 10_000*I (Source, 6) -
                              1_000*I (Source, 7) - 100*I (Source, 8) -
                              10*I (Source, 9) - I (Source, 10));

      procedure Calculate_Negative_Target_For_Length_11_Case_1_XXX_XXX_XXX (Source     : in  String_T;
                                                                            Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 1)..(Source'First + 10)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 1)..(Source'First + 10) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := -N(Source'First + 10);
         Target := Target - N(Source'First + 9) *            10;
         Target := Target - N(Source'First + 8) *           100;
         Target := Target - N(Source'First + 7) *         1_000;
         Target := Target - N(Source'First + 6) *        10_000;
         Target := Target - N(Source'First + 5) *       100_000;
         Target := Target - N(Source'First + 4) *     1_000_000;
         Target := Target - N(Source'First + 3) *    10_000_000;
         Target := Target - N(Source'First + 2) *   100_000_000;
         Target := Target - N(Source'First + 1) * 1_000_000_000;
      end Calculate_Negative_Target_For_Length_11_Case_1_XXX_XXX_XXX;

      procedure Calculate_Negative_Target_Length_10 (Source     : in  String_T;
                                                     Target     : out Int32_T);
      pragma Precondition (Source'Length = 10 and then (Source(Source'First + 0) = '-' and
                             (for all Index in (Source'First + 1)..(Source'First + 9) => Character.Is_Digit (Source (Index)))));
      pragma Postcondition (Target = -100_000_000*Character.To_Int32 (Source (Source'First + 1))
                            - 10_000_000*Character.To_Int32 (Source (Source'First + 2))
                            - 1_000_000*Character.To_Int32 (Source (Source'First + 3))
                            - 100_000*Character.To_Int32 (Source (Source'First + 4))
                            - 10_000*Character.To_Int32 (Source (Source'First + 5))
                            - 1_000*Character.To_Int32 (Source (Source'First + 6))
                            - 100*Character.To_Int32 (Source (Source'First + 7))
                            - 10*Character.To_Int32 (Source (Source'First + 8))
                            - Character.To_Int32 (Source (Source'First + 9)));

      procedure Calculate_Negative_Target_Length_10 (Source     : in  String_T;
                                                     Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 1)..(Source'First + 9)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 1)..(Source'First + 9) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := -N(Source'First + 9);
         Target := Target - N(Source'First + 8) *            10;
         Target := Target - N(Source'First + 7) *           100;
         Target := Target - N(Source'First + 6) *         1_000;
         Target := Target - N(Source'First + 5) *        10_000;
         Target := Target - N(Source'First + 4) *       100_000;
         Target := Target - N(Source'First + 3) *     1_000_000;
         Target := Target - N(Source'First + 2) *    10_000_000;
         Target := Target - N(Source'First + 1) *   100_000_000;
      end Calculate_Negative_Target_Length_10;

      procedure Calculate_Negative_Target_Length_9 (Source     : in  String_T;
                                                    Target     : out Int32_T);
      pragma Precondition (Source'Length = 9 and then (Source(Source'First + 0) = '-' and
                             (for all Index in (Source'First + 1)..(Source'First + 8) => Character.Is_Digit (Source (Index)))));
      pragma Postcondition (Target = -10_000_000*Character.To_Int32 (Source (Source'First + 1))
                            - 1000_000*Character.To_Int32 (Source (Source'First + 2))
                            - 100_000*Character.To_Int32 (Source (Source'First + 3))
                            - 10_000*Character.To_Int32 (Source (Source'First + 4))
                            - 1_000*Character.To_Int32 (Source (Source'First + 5))
                            - 100*Character.To_Int32 (Source (Source'First + 6))
                            - 10*Character.To_Int32 (Source (Source'First + 7))
                            - Character.To_Int32 (Source (Source'First + 8)));

      procedure Calculate_Negative_Target_Length_9 (Source     : in  String_T;
                                                    Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 1)..(Source'First + 8)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 1)..(Source'First + 8) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := -N(Source'First + 8);
         Target := Target - N(Source'First + 7) *            10;
         Target := Target - N(Source'First + 6) *           100;
         Target := Target - N(Source'First + 5) *         1_000;
         Target := Target - N(Source'First + 4) *        10_000;
         Target := Target - N(Source'First + 3) *       100_000;
         Target := Target - N(Source'First + 2) *     1_000_000;
         Target := Target - N(Source'First + 1) *    10_000_000;
      end Calculate_Negative_Target_Length_9;

      procedure Calculate_Negative_Target_Length_8 (Source     : in  String_T;
                                                    Target     : out Int32_T);
      pragma Precondition (Source'Length = 8 and then (Source(Source'First + 0) = '-' and
                             (for all Index in (Source'First + 1)..(Source'First + 7) => Character.Is_Digit (Source (Index)))));
      pragma Postcondition (Target = -1_000_000*Character.To_Int32 (Source (Source'First + 1))
                            - 100_000*Character.To_Int32 (Source (Source'First + 2))
                            - 10_000*Character.To_Int32 (Source (Source'First + 3))
                            - 1_000*Character.To_Int32 (Source (Source'First + 4))
                            - 100*Character.To_Int32 (Source (Source'First + 5))
                            - 10*Character.To_Int32 (Source (Source'First + 6))
                            - Character.To_Int32 (Source (Source'First + 7)));

      procedure Calculate_Negative_Target_Length_8 (Source     : in  String_T;
                                                    Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 1)..(Source'First + 7)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 1)..(Source'First + 7) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := -N(Source'First + 7);
         Target := Target - N(Source'First + 6) *            10;
         Target := Target - N(Source'First + 5) *           100;
         Target := Target - N(Source'First + 4) *         1_000;
         Target := Target - N(Source'First + 3) *        10_000;
         Target := Target - N(Source'First + 2) *       100_000;
         Target := Target - N(Source'First + 1) *     1_000_000;
      end Calculate_Negative_Target_Length_8;

      procedure Calculate_Negative_Target_Length_7 (Source     : in  String_T;
                                                    Target     : out Int32_T);
      pragma Precondition (Source'Length = 7 and then (Source(Source'First + 0) = '-' and
                             (for all Index in (Source'First + 1)..(Source'First + 6) => Character.Is_Digit (Source (Index)))));
      pragma Postcondition (Target = -100_000*Character.To_Int32 (Source (Source'First + 1))
                            - 10_000*Character.To_Int32 (Source (Source'First + 2))
                            - 1_000*Character.To_Int32 (Source (Source'First + 3))
                            - 100*Character.To_Int32 (Source (Source'First + 4))
                            - 10*Character.To_Int32 (Source (Source'First + 5))
                            - Character.To_Int32 (Source (Source'First + 6)));

      procedure Calculate_Negative_Target_Length_7 (Source     : in  String_T;
                                                    Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 1)..(Source'First + 6)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 1)..(Source'First + 6) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := -N(Source'First + 6);
         Target := Target - N(Source'First + 5) *            10;
         Target := Target - N(Source'First + 4) *           100;
         Target := Target - N(Source'First + 3) *         1_000;
         Target := Target - N(Source'First + 2) *        10_000;
         Target := Target - N(Source'First + 1) *       100_000;
      end Calculate_Negative_Target_Length_7;

      procedure Calculate_Negative_Target_Length_6 (Source     : in  String_T;
                                                    Target     : out Int32_T);
      pragma Precondition (Source'Length = 6 and then (Source(Source'First + 0) = '-' and
                             (for all Index in (Source'First + 1)..(Source'First + 5) => Character.Is_Digit (Source (Index)))));
      pragma Postcondition (Target = -10_000*Character.To_Int32 (Source (Source'First + 1))
                            - 1_000*Character.To_Int32 (Source (Source'First + 2))
                            - 100*Character.To_Int32 (Source (Source'First + 3))
                            - 10*Character.To_Int32 (Source (Source'First + 4))
                            - Character.To_Int32 (Source (Source'First + 5)));

      procedure Calculate_Negative_Target_Length_6 (Source     : in  String_T;
                                                    Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 1)..(Source'First + 5)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 1)..(Source'First + 5) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := -N(Source'First + 5);
         Target := Target - N(Source'First + 4) *            10;
         Target := Target - N(Source'First + 3) *           100;
         Target := Target - N(Source'First + 2) *         1_000;
         Target := Target - N(Source'First + 1) *        10_000;
      end Calculate_Negative_Target_Length_6;

      procedure Calculate_Negative_Target_Length_5 (Source     : in  String_T;
                                                    Target     : out Int32_T);
      pragma Precondition (Source'Length = 5 and then (Source(Source'First + 0) = '-' and
                             (for all Index in (Source'First + 1)..(Source'First + 4) => Character.Is_Digit (Source (Index)))));
      pragma Postcondition (Target = -1_000*Character.To_Int32 (Source (Source'First + 1))
                            - 100*Character.To_Int32 (Source (Source'First + 2))
                            - 10*Character.To_Int32 (Source (Source'First + 3))
                            - Character.To_Int32 (Source (Source'First + 4)));

      procedure Calculate_Negative_Target_Length_5 (Source     : in  String_T;
                                                    Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 1)..(Source'First + 4)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 1)..(Source'First + 4) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := -N(Source'First + 4);
         Target := Target - N(Source'First + 3) *            10;
         Target := Target - N(Source'First + 2) *           100;
         Target := Target - N(Source'First + 1) *         1_000;
      end Calculate_Negative_Target_Length_5;

      procedure Calculate_Negative_Target_Length_4 (Source     : in  String_T;
                                                    Target     : out Int32_T);
      pragma Precondition (Source'Length = 4 and then (Source(Source'First + 0) = '-' and
                             (for all Index in (Source'First + 1)..(Source'First + 3) => Character.Is_Digit (Source (Index)))));
      pragma Postcondition (Target = -100*Character.To_Int32 (Source (Source'First + 1))
                            - 10*Character.To_Int32 (Source (Source'First + 2))
                            - Character.To_Int32 (Source (Source'First + 3)));

      procedure Calculate_Negative_Target_Length_4 (Source     : in  String_T;
                                                    Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 1)..(Source'First + 3)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 1)..(Source'First + 3) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := -N(Source'First + 3);
         Target := Target - N(Source'First + 2) *            10;
         Target := Target - N(Source'First + 1) *           100;
      end Calculate_Negative_Target_Length_4;

      procedure Calculate_Negative_Target_Length_3 (Source     : in  String_T;
                                                    Target     : out Int32_T);
        pragma Precondition (Source'Length = 3 and then (Source(Source'First + 0) = '-' and
                               (for all Index in (Source'First + 1)..(Source'First + 2) => Character.Is_Digit (Source (Index)))));
      pragma Postcondition (Target = -10*Character.To_Int32 (Source (Source'First + 1)) - Character.To_Int32 (Source (Source'First + 2)));

      procedure Calculate_Negative_Target_Length_3 (Source     : in  String_T;
                                                    Target     : out Int32_T)
      is
         type Number_Array_Type is array (Positive range (Source'First + 1)..(Source'First + 2)) of Int32_T;

         N : Number_Array_Type := (others => 0);
      begin
         for Index in Positive range (Source'First + 1)..(Source'First + 2) loop
            To_Int32 (Source => Source (Index),
                      Target => N (Index));
         end loop;

         Target := -N(Source'First + 2);
         Target := Target - N(Source'First + 1) *            10;
      end Calculate_Negative_Target_Length_3;

      procedure Calculate_Negative_Target_Length_2 (Source     : in  String_T;
                                                    Target     : out Int32_T);
      pragma Precondition (Source'Length = 2 and then (Source(Source'First + 0) = '-' and
                             (for all Index in (Source'First + 1)..(Source'First + 1) => Character.Is_Digit (Source (Index)))));
      pragma Postcondition (Target = -Character.To_Int32 (Source (Source'First + 1)));

      procedure Calculate_Negative_Target_Length_2 (Source     : in  String_T;
                                                    Target     : out Int32_T) is
      begin
         To_Int32 (Source => Source (Source'First + 1),
                   Target => Target);

         Target := -Target;
      end Calculate_Negative_Target_Length_2;

      procedure Calculate_Negative_Target_Length_11 (Source     : in     String_T;
                                                     Target     : in out Int32_T;
                                                     Has_Failed :    out Boolean);
      pragma Precondition ((Target = 0 and (Source'Length = 11 and then ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))))));
      pragma Postcondition ((if (Source(Source'First + 1) = '2' and
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
                                   Has_Failed));

      procedure Calculate_Negative_Target_Length_11 (Source     : in     String_T;
                                                     Target     : in out Int32_T;
                                                     Has_Failed :    out Boolean) is
      begin
         if Source (Source'First + 1) > '2' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 1) < '2' then
            Calculate_Negative_Target_For_Length_11_Case_1_XXX_XXX_XXX (Source,
                                                                        Target);

            Has_Failed := False;
            return;
         end if;

         if Source (Source'First + 2) > '1' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 2) < '1' then
            Calculate_Negative_Target_For_Length_11_Case_2_0XX_XXX_XXX (Source,
                                                                        Target);

            Has_Failed := False;
            return;
         end if;

         if Source (Source'First + 3) > '4' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 3) < '4' then
            Calculate_Negative_Target_For_Length_11_Case_2_13X_XXX_XXX (Source,
                                                                        Target);

            Has_Failed := False;
            return;
         end if;

         if Source (Source'First + 4) > '7' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 4) < '7' then
            Calculate_Negative_Target_For_Length_11_Case_2_146_XXX_XXX (Source,
                                                                        Target);
            Has_Failed := False;
            return;
         end if;

         if Source (Source'First + 5) > '4' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 5) < '4' then
            Calculate_Negative_Target_For_Length_11_Case_2_147_3XX_XXX (Source,
                                                                        Target);
            Has_Failed := False;
            return;
         end if;

         if Source (Source'First + 6) > '8' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 6) < '8' then
            Calculate_Negative_Target_For_Length_11_Case_2_147_47X_XXX (Source,
                                                                        Target);
            Has_Failed := False;
            return;
         end if;

         if Source (Source'First + 7) > '3' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 7) < '3' then
            Calculate_Negative_Target_For_Length_11_Case_2_147_482_XXX (Source,
                                                                        Target);
            Has_Failed := False;
            return;
         end if;

         if Source (Source'First + 8) > '6' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 8) < '6' then
            Calculate_Negative_Target_For_Length_11_Case_2_147_483_5XX (Source,
                                                                        Target);
            Has_Failed := False;
            return;
         end if;

         if Source (Source'First + 9) > '4' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 9) < '4' then
            Calculate_Negative_Target_For_Length_11_Case_2_147_483_63X (Source,
                                                                        Target);
            Has_Failed := False;
            return;
         end if;

         if Source (Source'First + 10) > '8' then
            Has_Failed := True;
            return;
         end if;

         Calculate_Negative_Target_For_Length_11_Case_2_147_483_648 (Source,
                                                                     Target);
         Has_Failed := False;

      end Calculate_Negative_Target_Length_11;

      procedure Calculate_Negative_Target_Lengths_2_to_10 (Source     : in     String_T;
                                                           Target     : in out Int32_T;
                                                           Has_Failed :    out Boolean);
      pragma Precondition ((Target = 0 and ((Source'Length >= 2 and Source'Length <= 10) and then ((Source (Source'First) = '-') and (for all Index in Integer range (Source'First + 1) .. Source'Last => Character.Is_Digit (Source (Index)))))));
      pragma Contract_Cases ((Source'Length = 2 => (Target = -I (Source, 1)),
                              Source'Length = 3 => (Target = -10*I (Source, 1) - I (Source, 2)),
                              Source'Length = 4 => (Target = -100*I (Source, 1) - 10*I (Source, 2) - I (Source, 3)),
                              Source'Length = 5 => (Target = -1_000*I (Source, 1) - 100*I (Source, 2) - 10*I (Source, 3) - I (Source, 4)),
                              Source'Length = 6 => (Target = -10_000*I (Source, 1) - 1_000*I (Source, 2) - 100*I (Source, 3) - 10*I (Source, 4) - I (Source, 5)),
                              Source'Length = 7 => (Target = -100_000*I (Source, 1) - 10_000*I (Source, 2) - 1_000*I (Source, 3) - 100*I (Source, 4) - 10*I (Source, 5) - I (Source, 6)),
                              Source'Length = 8 => (Target = -1_000_000*I (Source, 1) - 100_000*I (Source, 2) - 10_000*I (Source, 3) - 1_000*I (Source, 4) - 100*I (Source, 5) - 10*I (Source, 6) - I (Source, 7)),
                              Source'Length = 9 => (Target = -10_000_000*I (Source, 1) - 1_000_000*I (Source, 2) - 100_000*I (Source, 3) - 10_000*I (Source, 4) - 1_000*I (Source, 5) - 100*I (Source, 6) - 10*I (Source, 7) - I (Source, 8)),
                              Source'Length = 10 => (Target = -100_000_000*I (Source, 1) - 10_000_000*I (Source, 2) - 1_000_000*I (Source, 3) - 100_000*I (Source, 4) - 10_000*I (Source, 5) - 1_000*I (Source, 6) - 100*I (Source, 7) - 10*I (Source, 8) - I (Source, 9))));

      procedure Calculate_Negative_Target_Lengths_2_to_10 (Source     : in     String_T;
                                                           Target     : in out Int32_T;
                                                           Has_Failed :    out Boolean) is
      begin
         case Source'Length is
            when 2 =>
               Calculate_Negative_Target_Length_2 (Source,
                                                   Target);
               Has_Failed := False;
            when 3 =>
               Calculate_Negative_Target_Length_3 (Source,
                                                   Target);
               Has_Failed := False;
            when 4 =>
               Calculate_Negative_Target_Length_4 (Source,
                                                   Target);
               Has_Failed := False;
            when 5 =>
               Calculate_Negative_Target_Length_5 (Source,
                                                   Target);
               Has_Failed := False;
            when 6 =>
               Calculate_Negative_Target_Length_6 (Source,
                                                   Target);
               Has_Failed := False;
            when 7 =>
               Calculate_Negative_Target_Length_7 (Source,
                                                   Target);
               Has_Failed := False;
            when 8 =>
               Calculate_Negative_Target_Length_8 (Source,
                                                   Target);
               Has_Failed := False;
            when 9 =>
               Calculate_Negative_Target_Length_9 (Source,
                                                   Target);
               Has_Failed := False;
            when 10 =>
               Calculate_Negative_Target_Length_10 (Source,
                                                    Target);
               Has_Failed := False;
            when others =>
               Target := 0;
               Has_Failed := True;
         end case;

      end Calculate_Negative_Target_Lengths_2_to_10;

      procedure Calculate_Positive_Target_Length_10 (Source     : in     String_T;
                                                     Target     :    out Int32_T;
                                                     Has_Failed :    out Boolean);
      pragma Precondition ((Source'Length = 10 and then (for all Index in Integer range (Source'First) .. Source'Last => Character.Is_Digit (Source (Index)))));
      pragma Postcondition ((if (Source(Source'First + 0) = '2' and
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
                                  Has_Failed));

      procedure Calculate_Positive_Target_Length_10 (Source     : in     String_T;
                                                     Target     :    out Int32_T;
                                                     Has_Failed :    out Boolean) is
      begin
         Target := 0;

         if Source (Source'First) > '2' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First) < '2' then
            Calculate_Positive_Target_For_Length_10_Case_1_XXX_XXX_XXX (Source,
                                                                        Target);
            Has_Failed := False;

            return;
         end if;

         if Source (Source'First + 1) > '1' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 1) < '1' then
            Calculate_Positive_Target_For_Length_10_Case_2_0XX_XXX_XXX (Source,
                                                                        Target);
            Has_Failed := False;
            return;
         end if;

         if Source (Source'First + 2) > '4' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 2) < '4' then
            Calculate_Positive_Target_For_Length_10_Case_2_13X_XXX_XXX (Source,
                                                                        Target);
            Has_Failed := False;
            return;
         end if;

         if Source (Source'First + 3) > '7' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 3) < '7' then
            Calculate_Positive_Target_For_Length_10_Case_2_146_XXX_XXX (Source,
                                                                        Target);
            Has_Failed := False;
            return;
         end if;

         if Source (Source'First + 4) > '4' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 4) < '4' then
            Calculate_Positive_Target_For_Length_10_Case_2_147_3XX_XXX (Source,
                                                                        Target);
            Has_Failed := False;
            return;
         end if;

         if Source (Source'First + 5) > '8' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 5) < '8' then
            Calculate_Positive_Target_For_Length_10_Case_2_147_47X_XXX (Source,
                                                                        Target);
            Has_Failed := False;
            return;
         end if;

         if Source (Source'First + 6) > '3' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 6) < '3' then
            Calculate_Positive_Target_For_Length_10_Case_2_147_482_XXX (Source,
                                                                        Target);
            Has_Failed := False;
            return;
         end if;

         if Source (Source'First + 7) > '6' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 7) < '6' then
            Calculate_Positive_Target_For_Length_10_Case_2_147_483_5XX (Source,
                                                                        Target);
            Has_Failed := False;
            return;
         end if;

         if Source (Source'First + 8) > '4' then
            Has_Failed := True;
            return;
         end if;

         if Source (Source'First + 8) < '4' then
            Calculate_Positive_Target_For_Length_10_Case_2_147_483_63X (Source,
                                                                        Target);
            Has_Failed := False;
            return;
         end if;

         if Source (Source'First + 9) > '7' then
            Has_Failed := True;
            return;
         end if;

         Calculate_Positive_Target_For_Length_10_Case_2_147_483_647 (Source,
                                                                     Target);
         Has_Failed := False;
      end Calculate_Positive_Target_Length_10;

      procedure Calculate_Positive_Target_Lengths_1_to_9 (Source     : in     String_T;
                                                          Target     :    out Int32_T;
                                                          Has_Failed :    out Boolean);
      pragma Precondition (Source'Length >= 1 and Source'Length <= 9 and (for all I in Positive range (Source'First)..Source'Last => Is_Digit (Source (I))));
      pragma Contract_Cases ((Source'Length = 1 => (Has_Failed = False and Target = I (Source, 0)),
                              Source'Length = 2 => (Has_Failed = False and Target = 10*I (Source, 0) + I (Source, 1)),
                              Source'Length = 3 => (Has_Failed = False and Target = 100*I (Source, 0) + 10*I (Source, 1) + I (Source, 2)),
                              Source'Length = 4 => (Has_Failed = False and
                                                         Target = 1_000*I (Source, 0) + 100*I (Source, 1) + 10*I (Source, 2) + I (Source, 3)),
                              Source'Length = 5 => (Has_Failed = False and
                                                         Target = 10_000*I (Source, 0) + 1_000*I (Source, 1) + 100*I (Source, 2) + 10*I (Source, 3) + I (Source, 4)),
                              Source'Length = 6 => (Has_Failed = False and
                                                         Target = 100_000*I (Source, 0) + 10_000*I (Source, 1) + 1_000*I (Source, 2) + 100*I (Source, 3) + 10*I (Source, 4) + I (Source, 5)),
                              Source'Length = 7 => (Has_Failed = False and
                                                         Target = 1_000_000*I (Source, 0) + 100_000*I (Source, 1) + 10_000*I (Source, 2) + 1_000*I (Source, 3) + 100*I (Source, 4) + 10*I (Source, 5) + I (Source, 6)),
                              Source'Length = 8 => (Has_Failed = False and
                                                         Target = 10_000_000*I (Source, 0) + 1_000_000*I (Source, 1) + 100_000*I (Source, 2) + 10_000*I (Source, 3) + 1_000*I (Source, 4) + 100*I (Source, 5) + 10*I (Source, 6) + I (Source, 7)),
                              Source'Length = 9 => (Has_Failed = False and
                                                         Target = 100_000_000*I (Source, 0) + 10_000_000*I (Source, 1) + 1_000_000*I (Source, 2) + 100_000*I (Source, 3) + 10_000*I (Source, 4) + 1_000*I (Source, 5) + 100*I (Source, 6) + 10*I (Source, 7) + I (Source, 8))));

      procedure Calculate_Positive_Target_Lengths_1_to_9 (Source     : in     String_T;
                                                          Target     :    out Int32_T;
                                                          Has_Failed :    out Boolean) is
      begin
         case Source'Length is
            when 1 =>
               Calculate_Positive_Target_Length_1 (Source,
                                                   Target);
               Has_Failed := False;
            when 2 =>
               Calculate_Positive_Target_Length_2 (Source,
                                                   Target);
               Has_Failed := False;
            when 3 =>
               Calculate_Positive_Target_Length_3 (Source,
                                                   Target);
               Has_Failed := False;
            when 4 =>
               Calculate_Positive_Target_Length_4 (Source,
                                                   Target);
               Has_Failed := False;
            when 5 =>
               Calculate_Positive_Target_Length_5 (Source,
                                                   Target);
               Has_Failed := False;
            when 6 =>
               Calculate_Positive_Target_Length_6 (Source,
                                                   Target);
               Has_Failed := False;
            when 7 =>
               Calculate_Positive_Target_Length_7 (Source,
                                                   Target);
               Has_Failed := False;
            when 8 =>
               Calculate_Positive_Target_Length_8 (Source,
                                                   Target);
               Has_Failed := False;
            when 9 =>
               Calculate_Positive_Target_Length_9 (Source,
                                                   Target);
               Has_Failed := False;
            when others =>
               Target := 0;
               Has_Failed := True;
         end case;

      end Calculate_Positive_Target_Lengths_1_to_9;

      procedure To_Int32 (Source     : in  String_T;
                          Target     : out Int32_T;
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

            for I in Positive range (Source'First + 1)..Source'Last loop
               if not Is_Digit (Source(I)) then
                  Target := 0;
                  Has_Failed := True;
                  return;
               end if;

               pragma Loop_Invariant (for all J in Positive range (Source'First + 1)..I => Is_Digit (Source (J)));
            end loop;

            Target := 0;

            if Source'Length = 11 then
               Calculate_Negative_Target_Length_11 (Source, Target, Has_Failed);
            else
               Calculate_Negative_Target_Lengths_2_to_10 (Source, Target, Has_Failed);
            end if;
         else
            if Source'Length > 10 then
               Target := 0;
               Has_Failed := True;
               return;
            end if;

            for I in Positive range Source'First..Source'Last loop
               if not Is_Digit (Source(I)) then
                  Target := 0;
                  Has_Failed := True;
                  return;
               end if;

               pragma Loop_Invariant (for all J in Positive range (Source'First)..I => Is_Digit (Source (J)));
            end loop;

            if Source'Length = 10 then
               Calculate_Positive_Target_Length_10 (Source, Target, Has_Failed);
            else
               Calculate_Positive_Target_Lengths_1_to_9 (Source, Target, Has_Failed);
            end if;
         end if;
      end To_Int32;

      function To_Int32 (Source : T) return Int32_T is
         Target : Int32_T;
      begin
         if Source (Source'First) = '-' then

            if Source'Length = 11 then
               if Source (Source'First + 1) < '2' then
                  Calculate_Negative_Target_For_Length_11_Case_1_XXX_XXX_XXX (Source,
                                                                              Target);
               elsif Source (Source'First + 2) < '1' then
                  Calculate_Negative_Target_For_Length_11_Case_2_0XX_XXX_XXX (Source,
                                                                              Target);
               elsif Source (Source'First + 3) < '4' then
                  Calculate_Negative_Target_For_Length_11_Case_2_13X_XXX_XXX (Source,
                                                                              Target);
               elsif Source (Source'First + 4) < '7' then
                  Calculate_Negative_Target_For_Length_11_Case_2_146_XXX_XXX (Source,
                                                                              Target);
               elsif Source (Source'First + 5) < '4' then
                  Calculate_Negative_Target_For_Length_11_Case_2_147_3XX_XXX (Source,
                                                                              Target);
               elsif Source (Source'First + 6) < '8' then
                  Calculate_Negative_Target_For_Length_11_Case_2_147_47X_XXX (Source,
                                                                              Target);
               elsif Source (Source'First + 7) < '3' then
                  Calculate_Negative_Target_For_Length_11_Case_2_147_482_XXX (Source,
                                                                              Target);
               elsif Source (Source'First + 8) < '6' then
                  Calculate_Negative_Target_For_Length_11_Case_2_147_483_5XX (Source,
                                                                              Target);
               elsif Source (Source'First + 9) < '4' then
                  Calculate_Negative_Target_For_Length_11_Case_2_147_483_63X (Source,
                                                                              Target);
               else
                  Calculate_Negative_Target_For_Length_11_Case_2_147_483_648 (Source,
                                                                              Target);
               end if;
            else
               case Source'Length is
               when 2 =>
                  Calculate_Negative_Target_Length_2 (Source,
                                                      Target);
               when 3 =>
                  Calculate_Negative_Target_Length_3 (Source,
                                                      Target);
               when 4 =>
                  Calculate_Negative_Target_Length_4 (Source,
                                                      Target);
               when 5 =>
                  Calculate_Negative_Target_Length_5 (Source,
                                                      Target);
               when 6 =>
                  Calculate_Negative_Target_Length_6 (Source,
                                                      Target);
               when 7 =>
                  Calculate_Negative_Target_Length_7 (Source,
                                                      Target);
               when 8 =>
                  Calculate_Negative_Target_Length_8 (Source,
                                                      Target);
               when 9 =>
                  Calculate_Negative_Target_Length_9 (Source,
                                                      Target);
               when 10 =>
                  Calculate_Negative_Target_Length_10 (Source,
                                                       Target);
               when others =>
                  Target := 0;
               end case;
            end if;
         else
            if Source'Length = 10 then
               if Source (Source'First) < '2' then
                  Calculate_Positive_Target_For_Length_10_Case_1_XXX_XXX_XXX (Source,
                                                                              Target);

               elsif Source (Source'First + 1) < '1' then
                  Calculate_Positive_Target_For_Length_10_Case_2_0XX_XXX_XXX (Source,
                                                                              Target);
               elsif Source (Source'First + 2) < '4' then
                  Calculate_Positive_Target_For_Length_10_Case_2_13X_XXX_XXX (Source,
                                                                              Target);
               elsif Source (Source'First + 3) < '7' then
                  Calculate_Positive_Target_For_Length_10_Case_2_146_XXX_XXX (Source,
                                                                              Target);
               elsif Source (Source'First + 4) < '4' then
                  Calculate_Positive_Target_For_Length_10_Case_2_147_3XX_XXX (Source,
                                                                              Target);
               elsif Source (Source'First + 5) < '8' then
                  Calculate_Positive_Target_For_Length_10_Case_2_147_47X_XXX (Source,
                                                                              Target);
               elsif Source (Source'First + 6) < '3' then
                  Calculate_Positive_Target_For_Length_10_Case_2_147_482_XXX (Source,
                                                                              Target);
               elsif Source (Source'First + 7) < '6' then
                  Calculate_Positive_Target_For_Length_10_Case_2_147_483_5XX (Source,
                                                                              Target);
               elsif Source (Source'First + 8) < '4' then
                  Calculate_Positive_Target_For_Length_10_Case_2_147_483_63X (Source,
                                                                              Target);
               else
                  Calculate_Positive_Target_For_Length_10_Case_2_147_483_647 (Source,
                                                                              Target);
               end if;
            else
               case Source'Length is
               when 1 =>
                  Calculate_Positive_Target_Length_1 (Source,
                                                      Target);
               when 2 =>
                  Calculate_Positive_Target_Length_2 (Source,
                                                      Target);
               when 3 =>
                  Calculate_Positive_Target_Length_3 (Source,
                                                      Target);
               when 4 =>
                  Calculate_Positive_Target_Length_4 (Source,
                                                      Target);
               when 5 =>
                  Calculate_Positive_Target_Length_5 (Source,
                                                      Target);
               when 6 =>
                  Calculate_Positive_Target_Length_6 (Source,
                                                      Target);
               when 7 =>
                  Calculate_Positive_Target_Length_7 (Source,
                                                      Target);
               when 8 =>
                  Calculate_Positive_Target_Length_8 (Source,
                                                      Target);
               when 9 =>
                  Calculate_Positive_Target_Length_9 (Source,
                                                      Target);
               when others =>
                  Target := 0;
               end case;
            end if;
         end if;

         return Target;
      end To_Int32;

      function Trim (This : T) return T is
      begin
         return T (Ada.Strings.Fixed.Trim (Source => Standard.String (This),
                                           Side   => Ada.Strings.Both));
      end Trim;

      procedure To_Standard_Out (This : T) is
      begin
         Ada.Text_IO.Put_Line (Standard.String (This));
      end To_Standard_Out;

      function Hash32 (This : T) return Hash32_T is
         H : Hash32_T := 0;
         A : Hash32_T := 31_415;
         B : constant Hash32_T := 27_183;
      begin
         for I in Positive range This'First..This'Last loop
            H := A*H + Standard.Character'Pos (This (I));
            A := A*B;
         end loop;

         return H;
      end Hash32;

   end String;

   package body Character is

      function Is_Digit (Char : T) return Boolean is
      begin
         return Char in '0'..'9';
      end Is_Digit;

      function To_Int32 (Source : in T) return Int32_T is
      begin
         return Int32_T (Standard.Character'Pos (Standard.Character (Source)) - Standard.Character'Pos ('0'));
      end To_Int32;

      procedure To_Int32 (Source : in  T;
                          Target : out Int32_T) is
      begin
         Target := Int32_T (Standard.Character'Pos (Standard.Character (Source)) - Standard.Character'Pos ('0'));
      end To_Int32;

   end Character;

   package body Int32 is

      function To_String (Value : T) return String_T is
      begin
         return String_T (Ada.Strings.Fixed.Trim (Source => Int32_T'Image (Value),
                                                  Side   => Ada.Strings.Both));
      end To_String;

      function To_String (Value : T) return Standard.String is
      begin
         return Ada.Strings.Fixed.Trim (Source => Int32_T'Image (Value),
                                        Side   => Ada.Strings.Both);
      end To_String;

      procedure To_Standard_Out (This : T) is
      begin
         Ada.Text_IO.Put_Line (Standard.String (Aida.String.Trim (String_T (Int32_T'Image (This)))));
      end To_Standard_Out;

   end Int32;

   -- The code in this package originates from the work of Dmitry A. Kazakov,
   -- the Simple Components library. The changes can be summarized:
   --
   --  - The subprograms have been grouped differently.
   --
   --  The original copyright notices:
   --                                                                    --
   --                                                                    --
   --  package Strings_Edit.UTF8       Copyright (c)  Dmitry A. Kazakov  --
   --  Interface                                      Luebeck            --
   --                                                 Spring, 2005       --
   --                                                                    --
   --                                Last revision :  21:03 21 Apr 2009  --
   --                                                                    --
   --  This  library  is  free software; you can redistribute it and/or  --
   --  modify it under the terms of the GNU General Public  License  as  --
   --  published by the Free Software Foundation; either version  2  of  --
   --  the License, or (at your option) any later version. This library  --
   --  is distributed in the hope that it will be useful,  but  WITHOUT  --
   --  ANY   WARRANTY;   without   even   the   implied   warranty   of  --
   --  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU  --
   --  General  Public  License  for  more  details.  You  should  have  --
   --  received  a  copy  of  the GNU General Public License along with  --
   --  this library; if not, write to  the  Free  Software  Foundation,  --
   --  Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.    --
   --                                                                    --
   --  As a special exception, if other files instantiate generics from  --
   --  this unit, or you link this unit with other files to produce  an  --
   --  executable, this unit does not by  itself  cause  the  resulting  --
   --  executable to be covered by the GNU General Public License. This  --
   --  exception  does not however invalidate any other reasons why the  --
   --  executable file might be covered by the GNU Public License.       --
   --
   --
   --
   --  package                         Copyright (c)  Dmitry A. Kazakov  --
   --     Strings_Edit.UTF8.Categorization            Luebeck            --
   --  Interface                                      Spring, 2008       --
   --                                                                    --
   --                                Last revision :  21:03 21 Apr 2009  --
   --                                                                    --
   --  This  library  is  free software; you can redistribute it and/or  --
   --  modify it under the terms of the GNU General Public  License  as  --
   --  published by the Free Software Foundation; either version  2  of  --
   --  the License, or (at your option) any later version. This library  --
   --  is distributed in the hope that it will be useful,  but  WITHOUT  --
   --  ANY   WARRANTY;   without   even   the   implied   warranty   of  --
   --  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU  --
   --  General  Public  License  for  more  details.  You  should  have  --
   --  received  a  copy  of  the GNU General Public License along with  --
   --  this library; if not, write to  the  Free  Software  Foundation,  --
   --  Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.    --
   --                                                                    --
   --  As a special exception, if other files instantiate generics from  --
   --  this unit, or you link this unit with other files to produce  an  --
   --  executable, this unit does not by  itself  cause  the  resulting  --
   --  executable to be covered by the GNU General Public License. This  --
   --  exception  does not however invalidate any other reasons why the  --
   --  executable file might be covered by the GNU Public License.       --
   --____________________________________________________________________--
   --
   --  This  package  provides  categorization of code points as defined by
   --  UnicodeData file.
   --

   package body UTF8_Code_Point is

      use Fs;

      type Categorization is record
         Code  : T;
         Upper : T;
         Lower : T;
      end record;
      type Categorization_Index is range 1..3070;
      type Categorization_Array is array (Categorization_Index) of Categorization;

      Mapping : constant Categorization_Array :=
        (
           (16#41#,16#41#,16#61#),(16#42#,16#42#,16#62#),(16#43#,16#43#,16#63#),
         (16#44#,16#44#,16#64#),(16#45#,16#45#,16#65#),(16#46#,16#46#,16#66#),
         (16#47#,16#47#,16#67#),(16#48#,16#48#,16#68#),(16#49#,16#49#,16#69#),
         (16#4A#,16#4A#,16#6A#),(16#4B#,16#4B#,16#6B#),(16#4C#,16#4C#,16#6C#),
         (16#4D#,16#4D#,16#6D#),(16#4E#,16#4E#,16#6E#),(16#4F#,16#4F#,16#6F#),
         (16#50#,16#50#,16#70#),(16#51#,16#51#,16#71#),(16#52#,16#52#,16#72#),
         (16#53#,16#53#,16#73#),(16#54#,16#54#,16#74#),(16#55#,16#55#,16#75#),
         (16#56#,16#56#,16#76#),(16#57#,16#57#,16#77#),(16#58#,16#58#,16#78#),
         (16#59#,16#59#,16#79#),(16#5A#,16#5A#,16#7A#),(16#61#,16#41#,16#61#),
         (16#62#,16#42#,16#62#),(16#63#,16#43#,16#63#),(16#64#,16#44#,16#64#),
         (16#65#,16#45#,16#65#),(16#66#,16#46#,16#66#),(16#67#,16#47#,16#67#),
         (16#68#,16#48#,16#68#),(16#69#,16#49#,16#69#),(16#6A#,16#4A#,16#6A#),
         (16#6B#,16#4B#,16#6B#),(16#6C#,16#4C#,16#6C#),(16#6D#,16#4D#,16#6D#),
         (16#6E#,16#4E#,16#6E#),(16#6F#,16#4F#,16#6F#),(16#70#,16#50#,16#70#),
         (16#71#,16#51#,16#71#),(16#72#,16#52#,16#72#),(16#73#,16#53#,16#73#),
         (16#74#,16#54#,16#74#),(16#75#,16#55#,16#75#),(16#76#,16#56#,16#76#),
         (16#77#,16#57#,16#77#),(16#78#,16#58#,16#78#),(16#79#,16#59#,16#79#),
         (16#7A#,16#5A#,16#7A#),(16#AA#,16#AA#,16#AA#),(16#B5#,16#39C#,16#B5#),
         (16#BA#,16#BA#,16#BA#),(16#C0#,16#C0#,16#E0#),(16#C1#,16#C1#,16#E1#),
         (16#C2#,16#C2#,16#E2#),(16#C3#,16#C3#,16#E3#),(16#C4#,16#C4#,16#E4#),
         (16#C5#,16#C5#,16#E5#),(16#C6#,16#C6#,16#E6#),(16#C7#,16#C7#,16#E7#),
         (16#C8#,16#C8#,16#E8#),(16#C9#,16#C9#,16#E9#),(16#CA#,16#CA#,16#EA#),
         (16#CB#,16#CB#,16#EB#),(16#CC#,16#CC#,16#EC#),(16#CD#,16#CD#,16#ED#),
         (16#CE#,16#CE#,16#EE#),(16#CF#,16#CF#,16#EF#),(16#D0#,16#D0#,16#F0#),
         (16#D1#,16#D1#,16#F1#),(16#D2#,16#D2#,16#F2#),(16#D3#,16#D3#,16#F3#),
         (16#D4#,16#D4#,16#F4#),(16#D5#,16#D5#,16#F5#),(16#D6#,16#D6#,16#F6#),
         (16#D8#,16#D8#,16#F8#),(16#D9#,16#D9#,16#F9#),(16#DA#,16#DA#,16#FA#),
         (16#DB#,16#DB#,16#FB#),(16#DC#,16#DC#,16#FC#),(16#DD#,16#DD#,16#FD#),
         (16#DE#,16#DE#,16#FE#),(16#DF#,16#DF#,16#DF#),(16#E0#,16#C0#,16#E0#),
         (16#E1#,16#C1#,16#E1#),(16#E2#,16#C2#,16#E2#),(16#E3#,16#C3#,16#E3#),
         (16#E4#,16#C4#,16#E4#),(16#E5#,16#C5#,16#E5#),(16#E6#,16#C6#,16#E6#),
         (16#E7#,16#C7#,16#E7#),(16#E8#,16#C8#,16#E8#),(16#E9#,16#C9#,16#E9#),
         (16#EA#,16#CA#,16#EA#),(16#EB#,16#CB#,16#EB#),(16#EC#,16#CC#,16#EC#),
         (16#ED#,16#CD#,16#ED#),(16#EE#,16#CE#,16#EE#),(16#EF#,16#CF#,16#EF#),
         (16#F0#,16#D0#,16#F0#),(16#F1#,16#D1#,16#F1#),(16#F2#,16#D2#,16#F2#),
         (16#F3#,16#D3#,16#F3#),(16#F4#,16#D4#,16#F4#),(16#F5#,16#D5#,16#F5#),
         (16#F6#,16#D6#,16#F6#),(16#F8#,16#D8#,16#F8#),(16#F9#,16#D9#,16#F9#),
         (16#FA#,16#DA#,16#FA#),(16#FB#,16#DB#,16#FB#),(16#FC#,16#DC#,16#FC#),
         (16#FD#,16#DD#,16#FD#),(16#FE#,16#DE#,16#FE#),(16#FF#,16#178#,16#FF#),
         (16#100#,16#100#,16#101#),(16#101#,16#100#,16#101#),(16#102#,16#102#,16#103#),
         (16#103#,16#102#,16#103#),(16#104#,16#104#,16#105#),(16#105#,16#104#,16#105#),
         (16#106#,16#106#,16#107#),(16#107#,16#106#,16#107#),(16#108#,16#108#,16#109#),
         (16#109#,16#108#,16#109#),(16#10A#,16#10A#,16#10B#),(16#10B#,16#10A#,16#10B#),
         (16#10C#,16#10C#,16#10D#),(16#10D#,16#10C#,16#10D#),(16#10E#,16#10E#,16#10F#),
         (16#10F#,16#10E#,16#10F#),(16#110#,16#110#,16#111#),(16#111#,16#110#,16#111#),
         (16#112#,16#112#,16#113#),(16#113#,16#112#,16#113#),(16#114#,16#114#,16#115#),
         (16#115#,16#114#,16#115#),(16#116#,16#116#,16#117#),(16#117#,16#116#,16#117#),
         (16#118#,16#118#,16#119#),(16#119#,16#118#,16#119#),(16#11A#,16#11A#,16#11B#),
         (16#11B#,16#11A#,16#11B#),(16#11C#,16#11C#,16#11D#),(16#11D#,16#11C#,16#11D#),
         (16#11E#,16#11E#,16#11F#),(16#11F#,16#11E#,16#11F#),(16#120#,16#120#,16#121#),
         (16#121#,16#120#,16#121#),(16#122#,16#122#,16#123#),(16#123#,16#122#,16#123#),
         (16#124#,16#124#,16#125#),(16#125#,16#124#,16#125#),(16#126#,16#126#,16#127#),
         (16#127#,16#126#,16#127#),(16#128#,16#128#,16#129#),(16#129#,16#128#,16#129#),
         (16#12A#,16#12A#,16#12B#),(16#12B#,16#12A#,16#12B#),(16#12C#,16#12C#,16#12D#),
         (16#12D#,16#12C#,16#12D#),(16#12E#,16#12E#,16#12F#),(16#12F#,16#12E#,16#12F#),
         (16#130#,16#130#,16#69#),(16#131#,16#49#,16#131#),(16#132#,16#132#,16#133#),
         (16#133#,16#132#,16#133#),(16#134#,16#134#,16#135#),(16#135#,16#134#,16#135#),
         (16#136#,16#136#,16#137#),(16#137#,16#136#,16#137#),(16#138#,16#138#,16#138#),
         (16#139#,16#139#,16#13A#),(16#13A#,16#139#,16#13A#),(16#13B#,16#13B#,16#13C#),
         (16#13C#,16#13B#,16#13C#),(16#13D#,16#13D#,16#13E#),(16#13E#,16#13D#,16#13E#),
         (16#13F#,16#13F#,16#140#),(16#140#,16#13F#,16#140#),(16#141#,16#141#,16#142#),
         (16#142#,16#141#,16#142#),(16#143#,16#143#,16#144#),(16#144#,16#143#,16#144#),
         (16#145#,16#145#,16#146#),(16#146#,16#145#,16#146#),(16#147#,16#147#,16#148#),
         (16#148#,16#147#,16#148#),(16#149#,16#149#,16#149#),(16#14A#,16#14A#,16#14B#),
         (16#14B#,16#14A#,16#14B#),(16#14C#,16#14C#,16#14D#),(16#14D#,16#14C#,16#14D#),
         (16#14E#,16#14E#,16#14F#),(16#14F#,16#14E#,16#14F#),(16#150#,16#150#,16#151#),
         (16#151#,16#150#,16#151#),(16#152#,16#152#,16#153#),(16#153#,16#152#,16#153#),
         (16#154#,16#154#,16#155#),(16#155#,16#154#,16#155#),(16#156#,16#156#,16#157#),
         (16#157#,16#156#,16#157#),(16#158#,16#158#,16#159#),(16#159#,16#158#,16#159#),
         (16#15A#,16#15A#,16#15B#),(16#15B#,16#15A#,16#15B#),(16#15C#,16#15C#,16#15D#),
         (16#15D#,16#15C#,16#15D#),(16#15E#,16#15E#,16#15F#),(16#15F#,16#15E#,16#15F#),
         (16#160#,16#160#,16#161#),(16#161#,16#160#,16#161#),(16#162#,16#162#,16#163#),
         (16#163#,16#162#,16#163#),(16#164#,16#164#,16#165#),(16#165#,16#164#,16#165#),
         (16#166#,16#166#,16#167#),(16#167#,16#166#,16#167#),(16#168#,16#168#,16#169#),
         (16#169#,16#168#,16#169#),(16#16A#,16#16A#,16#16B#),(16#16B#,16#16A#,16#16B#),
         (16#16C#,16#16C#,16#16D#),(16#16D#,16#16C#,16#16D#),(16#16E#,16#16E#,16#16F#),
         (16#16F#,16#16E#,16#16F#),(16#170#,16#170#,16#171#),(16#171#,16#170#,16#171#),
         (16#172#,16#172#,16#173#),(16#173#,16#172#,16#173#),(16#174#,16#174#,16#175#),
         (16#175#,16#174#,16#175#),(16#176#,16#176#,16#177#),(16#177#,16#176#,16#177#),
         (16#178#,16#178#,16#FF#),(16#179#,16#179#,16#17A#),(16#17A#,16#179#,16#17A#),
         (16#17B#,16#17B#,16#17C#),(16#17C#,16#17B#,16#17C#),(16#17D#,16#17D#,16#17E#),
         (16#17E#,16#17D#,16#17E#),(16#17F#,16#53#,16#17F#),(16#180#,16#243#,16#180#),
         (16#181#,16#181#,16#253#),(16#182#,16#182#,16#183#),(16#183#,16#182#,16#183#),
         (16#184#,16#184#,16#185#),(16#185#,16#184#,16#185#),(16#186#,16#186#,16#254#),
         (16#187#,16#187#,16#188#),(16#188#,16#187#,16#188#),(16#189#,16#189#,16#256#),
         (16#18A#,16#18A#,16#257#),(16#18B#,16#18B#,16#18C#),(16#18C#,16#18B#,16#18C#),
         (16#18D#,16#18D#,16#18D#),(16#18E#,16#18E#,16#1DD#),(16#18F#,16#18F#,16#259#),
         (16#190#,16#190#,16#25B#),(16#191#,16#191#,16#192#),(16#192#,16#191#,16#192#),
         (16#193#,16#193#,16#260#),(16#194#,16#194#,16#263#),(16#195#,16#1F6#,16#195#),
         (16#196#,16#196#,16#269#),(16#197#,16#197#,16#268#),(16#198#,16#198#,16#199#),
         (16#199#,16#198#,16#199#),(16#19A#,16#23D#,16#19A#),(16#19B#,16#19B#,16#19B#),
         (16#19C#,16#19C#,16#26F#),(16#19D#,16#19D#,16#272#),(16#19E#,16#220#,16#19E#),
         (16#19F#,16#19F#,16#275#),(16#1A0#,16#1A0#,16#1A1#),(16#1A1#,16#1A0#,16#1A1#),
         (16#1A2#,16#1A2#,16#1A3#),(16#1A3#,16#1A2#,16#1A3#),(16#1A4#,16#1A4#,16#1A5#),
         (16#1A5#,16#1A4#,16#1A5#),(16#1A6#,16#1A6#,16#280#),(16#1A7#,16#1A7#,16#1A8#),
         (16#1A8#,16#1A7#,16#1A8#),(16#1A9#,16#1A9#,16#283#),(16#1AA#,16#1AA#,16#1AA#),
         (16#1AB#,16#1AB#,16#1AB#),(16#1AC#,16#1AC#,16#1AD#),(16#1AD#,16#1AC#,16#1AD#),
         (16#1AE#,16#1AE#,16#288#),(16#1AF#,16#1AF#,16#1B0#),(16#1B0#,16#1AF#,16#1B0#),
         (16#1B1#,16#1B1#,16#28A#),(16#1B2#,16#1B2#,16#28B#),(16#1B3#,16#1B3#,16#1B4#),
         (16#1B4#,16#1B3#,16#1B4#),(16#1B5#,16#1B5#,16#1B6#),(16#1B6#,16#1B5#,16#1B6#),
         (16#1B7#,16#1B7#,16#292#),(16#1B8#,16#1B8#,16#1B9#),(16#1B9#,16#1B8#,16#1B9#),
         (16#1BA#,16#1BA#,16#1BA#),(16#1BC#,16#1BC#,16#1BD#),(16#1BD#,16#1BC#,16#1BD#),
         (16#1BE#,16#1BE#,16#1BE#),(16#1BF#,16#1F7#,16#1BF#),(16#1C4#,16#1C4#,16#1C6#),
         (16#1C5#,16#1C4#,16#1C6#),(16#1C6#,16#1C4#,16#1C6#),(16#1C7#,16#1C7#,16#1C9#),
         (16#1C8#,16#1C7#,16#1C9#),(16#1C9#,16#1C7#,16#1C9#),(16#1CA#,16#1CA#,16#1CC#),
         (16#1CB#,16#1CA#,16#1CC#),(16#1CC#,16#1CA#,16#1CC#),(16#1CD#,16#1CD#,16#1CE#),
         (16#1CE#,16#1CD#,16#1CE#),(16#1CF#,16#1CF#,16#1D0#),(16#1D0#,16#1CF#,16#1D0#),
         (16#1D1#,16#1D1#,16#1D2#),(16#1D2#,16#1D1#,16#1D2#),(16#1D3#,16#1D3#,16#1D4#),
         (16#1D4#,16#1D3#,16#1D4#),(16#1D5#,16#1D5#,16#1D6#),(16#1D6#,16#1D5#,16#1D6#),
         (16#1D7#,16#1D7#,16#1D8#),(16#1D8#,16#1D7#,16#1D8#),(16#1D9#,16#1D9#,16#1DA#),
         (16#1DA#,16#1D9#,16#1DA#),(16#1DB#,16#1DB#,16#1DC#),(16#1DC#,16#1DB#,16#1DC#),
         (16#1DD#,16#18E#,16#1DD#),(16#1DE#,16#1DE#,16#1DF#),(16#1DF#,16#1DE#,16#1DF#),
         (16#1E0#,16#1E0#,16#1E1#),(16#1E1#,16#1E0#,16#1E1#),(16#1E2#,16#1E2#,16#1E3#),
         (16#1E3#,16#1E2#,16#1E3#),(16#1E4#,16#1E4#,16#1E5#),(16#1E5#,16#1E4#,16#1E5#),
         (16#1E6#,16#1E6#,16#1E7#),(16#1E7#,16#1E6#,16#1E7#),(16#1E8#,16#1E8#,16#1E9#),
         (16#1E9#,16#1E8#,16#1E9#),(16#1EA#,16#1EA#,16#1EB#),(16#1EB#,16#1EA#,16#1EB#),
         (16#1EC#,16#1EC#,16#1ED#),(16#1ED#,16#1EC#,16#1ED#),(16#1EE#,16#1EE#,16#1EF#),
         (16#1EF#,16#1EE#,16#1EF#),(16#1F0#,16#1F0#,16#1F0#),(16#1F1#,16#1F1#,16#1F3#),
         (16#1F2#,16#1F1#,16#1F3#),(16#1F3#,16#1F1#,16#1F3#),(16#1F4#,16#1F4#,16#1F5#),
         (16#1F5#,16#1F4#,16#1F5#),(16#1F6#,16#1F6#,16#195#),(16#1F7#,16#1F7#,16#1BF#),
         (16#1F8#,16#1F8#,16#1F9#),(16#1F9#,16#1F8#,16#1F9#),(16#1FA#,16#1FA#,16#1FB#),
         (16#1FB#,16#1FA#,16#1FB#),(16#1FC#,16#1FC#,16#1FD#),(16#1FD#,16#1FC#,16#1FD#),
         (16#1FE#,16#1FE#,16#1FF#),(16#1FF#,16#1FE#,16#1FF#),(16#200#,16#200#,16#201#),
         (16#201#,16#200#,16#201#),(16#202#,16#202#,16#203#),(16#203#,16#202#,16#203#),
         (16#204#,16#204#,16#205#),(16#205#,16#204#,16#205#),(16#206#,16#206#,16#207#),
         (16#207#,16#206#,16#207#),(16#208#,16#208#,16#209#),(16#209#,16#208#,16#209#),
         (16#20A#,16#20A#,16#20B#),(16#20B#,16#20A#,16#20B#),(16#20C#,16#20C#,16#20D#),
         (16#20D#,16#20C#,16#20D#),(16#20E#,16#20E#,16#20F#),(16#20F#,16#20E#,16#20F#),
         (16#210#,16#210#,16#211#),(16#211#,16#210#,16#211#),(16#212#,16#212#,16#213#),
         (16#213#,16#212#,16#213#),(16#214#,16#214#,16#215#),(16#215#,16#214#,16#215#),
         (16#216#,16#216#,16#217#),(16#217#,16#216#,16#217#),(16#218#,16#218#,16#219#),
         (16#219#,16#218#,16#219#),(16#21A#,16#21A#,16#21B#),(16#21B#,16#21A#,16#21B#),
         (16#21C#,16#21C#,16#21D#),(16#21D#,16#21C#,16#21D#),(16#21E#,16#21E#,16#21F#),
         (16#21F#,16#21E#,16#21F#),(16#220#,16#220#,16#19E#),(16#221#,16#221#,16#221#),
         (16#222#,16#222#,16#223#),(16#223#,16#222#,16#223#),(16#224#,16#224#,16#225#),
         (16#225#,16#224#,16#225#),(16#226#,16#226#,16#227#),(16#227#,16#226#,16#227#),
         (16#228#,16#228#,16#229#),(16#229#,16#228#,16#229#),(16#22A#,16#22A#,16#22B#),
         (16#22B#,16#22A#,16#22B#),(16#22C#,16#22C#,16#22D#),(16#22D#,16#22C#,16#22D#),
         (16#22E#,16#22E#,16#22F#),(16#22F#,16#22E#,16#22F#),(16#230#,16#230#,16#231#),
         (16#231#,16#230#,16#231#),(16#232#,16#232#,16#233#),(16#233#,16#232#,16#233#),
         (16#234#,16#234#,16#234#),(16#235#,16#235#,16#235#),(16#236#,16#236#,16#236#),
         (16#237#,16#237#,16#237#),(16#238#,16#238#,16#238#),(16#239#,16#239#,16#239#),
         (16#23A#,16#23A#,16#2C65#),(16#23B#,16#23B#,16#23C#),(16#23C#,16#23B#,16#23C#),
         (16#23D#,16#23D#,16#19A#),(16#23E#,16#23E#,16#2C66#),(16#23F#,16#23F#,16#23F#),
         (16#240#,16#240#,16#240#),(16#241#,16#241#,16#242#),(16#242#,16#241#,16#242#),
         (16#243#,16#243#,16#180#),(16#244#,16#244#,16#289#),(16#245#,16#245#,16#28C#),
         (16#246#,16#246#,16#247#),(16#247#,16#246#,16#247#),(16#248#,16#248#,16#249#),
         (16#249#,16#248#,16#249#),(16#24A#,16#24A#,16#24B#),(16#24B#,16#24A#,16#24B#),
         (16#24C#,16#24C#,16#24D#),(16#24D#,16#24C#,16#24D#),(16#24E#,16#24E#,16#24F#),
         (16#24F#,16#24E#,16#24F#),(16#250#,16#250#,16#250#),(16#251#,16#251#,16#251#),
         (16#252#,16#252#,16#252#),(16#253#,16#181#,16#253#),(16#254#,16#186#,16#254#),
         (16#255#,16#255#,16#255#),(16#256#,16#189#,16#256#),(16#257#,16#18A#,16#257#),
         (16#258#,16#258#,16#258#),(16#259#,16#18F#,16#259#),(16#25A#,16#25A#,16#25A#),
         (16#25B#,16#190#,16#25B#),(16#25C#,16#25C#,16#25C#),(16#25D#,16#25D#,16#25D#),
         (16#25E#,16#25E#,16#25E#),(16#25F#,16#25F#,16#25F#),(16#260#,16#193#,16#260#),
         (16#261#,16#261#,16#261#),(16#262#,16#262#,16#262#),(16#263#,16#194#,16#263#),
         (16#264#,16#264#,16#264#),(16#265#,16#265#,16#265#),(16#266#,16#266#,16#266#),
         (16#267#,16#267#,16#267#),(16#268#,16#197#,16#268#),(16#269#,16#196#,16#269#),
         (16#26A#,16#26A#,16#26A#),(16#26B#,16#2C62#,16#26B#),(16#26C#,16#26C#,16#26C#),
         (16#26D#,16#26D#,16#26D#),(16#26E#,16#26E#,16#26E#),(16#26F#,16#19C#,16#26F#),
         (16#270#,16#270#,16#270#),(16#271#,16#271#,16#271#),(16#272#,16#19D#,16#272#),
         (16#273#,16#273#,16#273#),(16#274#,16#274#,16#274#),(16#275#,16#19F#,16#275#),
         (16#276#,16#276#,16#276#),(16#277#,16#277#,16#277#),(16#278#,16#278#,16#278#),
         (16#279#,16#279#,16#279#),(16#27A#,16#27A#,16#27A#),(16#27B#,16#27B#,16#27B#),
         (16#27C#,16#27C#,16#27C#),(16#27D#,16#2C64#,16#27D#),(16#27E#,16#27E#,16#27E#),
         (16#27F#,16#27F#,16#27F#),(16#280#,16#1A6#,16#280#),(16#281#,16#281#,16#281#),
         (16#282#,16#282#,16#282#),(16#283#,16#1A9#,16#283#),(16#284#,16#284#,16#284#),
         (16#285#,16#285#,16#285#),(16#286#,16#286#,16#286#),(16#287#,16#287#,16#287#),
         (16#288#,16#1AE#,16#288#),(16#289#,16#244#,16#289#),(16#28A#,16#1B1#,16#28A#),
         (16#28B#,16#1B2#,16#28B#),(16#28C#,16#245#,16#28C#),(16#28D#,16#28D#,16#28D#),
         (16#28E#,16#28E#,16#28E#),(16#28F#,16#28F#,16#28F#),(16#290#,16#290#,16#290#),
         (16#291#,16#291#,16#291#),(16#292#,16#1B7#,16#292#),(16#293#,16#293#,16#293#),
         (16#295#,16#295#,16#295#),(16#296#,16#296#,16#296#),(16#297#,16#297#,16#297#),
         (16#298#,16#298#,16#298#),(16#299#,16#299#,16#299#),(16#29A#,16#29A#,16#29A#),
         (16#29B#,16#29B#,16#29B#),(16#29C#,16#29C#,16#29C#),(16#29D#,16#29D#,16#29D#),
         (16#29E#,16#29E#,16#29E#),(16#29F#,16#29F#,16#29F#),(16#2A0#,16#2A0#,16#2A0#),
         (16#2A1#,16#2A1#,16#2A1#),(16#2A2#,16#2A2#,16#2A2#),(16#2A3#,16#2A3#,16#2A3#),
         (16#2A4#,16#2A4#,16#2A4#),(16#2A5#,16#2A5#,16#2A5#),(16#2A6#,16#2A6#,16#2A6#),
         (16#2A7#,16#2A7#,16#2A7#),(16#2A8#,16#2A8#,16#2A8#),(16#2A9#,16#2A9#,16#2A9#),
         (16#2AA#,16#2AA#,16#2AA#),(16#2AB#,16#2AB#,16#2AB#),(16#2AC#,16#2AC#,16#2AC#),
         (16#2AD#,16#2AD#,16#2AD#),(16#2AE#,16#2AE#,16#2AE#),(16#2AF#,16#2AF#,16#2AF#),
         (16#345#,16#399#,16#345#),(16#37B#,16#3FD#,16#37B#),(16#37C#,16#3FE#,16#37C#),
         (16#37D#,16#3FF#,16#37D#),(16#386#,16#386#,16#3AC#),(16#388#,16#388#,16#3AD#),
         (16#389#,16#389#,16#3AE#),(16#38A#,16#38A#,16#3AF#),(16#38C#,16#38C#,16#3CC#),
         (16#38E#,16#38E#,16#3CD#),(16#38F#,16#38F#,16#3CE#),(16#390#,16#390#,16#390#),
         (16#391#,16#391#,16#3B1#),(16#392#,16#392#,16#3B2#),(16#393#,16#393#,16#3B3#),
         (16#394#,16#394#,16#3B4#),(16#395#,16#395#,16#3B5#),(16#396#,16#396#,16#3B6#),
         (16#397#,16#397#,16#3B7#),(16#398#,16#398#,16#3B8#),(16#399#,16#399#,16#3B9#),
         (16#39A#,16#39A#,16#3BA#),(16#39B#,16#39B#,16#3BB#),(16#39C#,16#39C#,16#3BC#),
         (16#39D#,16#39D#,16#3BD#),(16#39E#,16#39E#,16#3BE#),(16#39F#,16#39F#,16#3BF#),
         (16#3A0#,16#3A0#,16#3C0#),(16#3A1#,16#3A1#,16#3C1#),(16#3A3#,16#3A3#,16#3C3#),
         (16#3A4#,16#3A4#,16#3C4#),(16#3A5#,16#3A5#,16#3C5#),(16#3A6#,16#3A6#,16#3C6#),
         (16#3A7#,16#3A7#,16#3C7#),(16#3A8#,16#3A8#,16#3C8#),(16#3A9#,16#3A9#,16#3C9#),
         (16#3AA#,16#3AA#,16#3CA#),(16#3AB#,16#3AB#,16#3CB#),(16#3AC#,16#386#,16#3AC#),
         (16#3AD#,16#388#,16#3AD#),(16#3AE#,16#389#,16#3AE#),(16#3AF#,16#38A#,16#3AF#),
         (16#3B0#,16#3B0#,16#3B0#),(16#3B1#,16#391#,16#3B1#),(16#3B2#,16#392#,16#3B2#),
         (16#3B3#,16#393#,16#3B3#),(16#3B4#,16#394#,16#3B4#),(16#3B5#,16#395#,16#3B5#),
         (16#3B6#,16#396#,16#3B6#),(16#3B7#,16#397#,16#3B7#),(16#3B8#,16#398#,16#3B8#),
         (16#3B9#,16#399#,16#3B9#),(16#3BA#,16#39A#,16#3BA#),(16#3BB#,16#39B#,16#3BB#),
         (16#3BC#,16#39C#,16#3BC#),(16#3BD#,16#39D#,16#3BD#),(16#3BE#,16#39E#,16#3BE#),
         (16#3BF#,16#39F#,16#3BF#),(16#3C0#,16#3A0#,16#3C0#),(16#3C1#,16#3A1#,16#3C1#),
         (16#3C2#,16#3A3#,16#3C2#),(16#3C3#,16#3A3#,16#3C3#),(16#3C4#,16#3A4#,16#3C4#),
         (16#3C5#,16#3A5#,16#3C5#),(16#3C6#,16#3A6#,16#3C6#),(16#3C7#,16#3A7#,16#3C7#),
         (16#3C8#,16#3A8#,16#3C8#),(16#3C9#,16#3A9#,16#3C9#),(16#3CA#,16#3AA#,16#3CA#),
         (16#3CB#,16#3AB#,16#3CB#),(16#3CC#,16#38C#,16#3CC#),(16#3CD#,16#38E#,16#3CD#),
         (16#3CE#,16#38F#,16#3CE#),(16#3D0#,16#392#,16#3D0#),(16#3D1#,16#398#,16#3D1#),
         (16#3D2#,16#3D2#,16#3D2#),(16#3D3#,16#3D3#,16#3D3#),(16#3D4#,16#3D4#,16#3D4#),
         (16#3D5#,16#3A6#,16#3D5#),(16#3D6#,16#3A0#,16#3D6#),(16#3D7#,16#3D7#,16#3D7#),
         (16#3D8#,16#3D8#,16#3D9#),(16#3D9#,16#3D8#,16#3D9#),(16#3DA#,16#3DA#,16#3DB#),
         (16#3DB#,16#3DA#,16#3DB#),(16#3DC#,16#3DC#,16#3DD#),(16#3DD#,16#3DC#,16#3DD#),
         (16#3DE#,16#3DE#,16#3DF#),(16#3DF#,16#3DE#,16#3DF#),(16#3E0#,16#3E0#,16#3E1#),
         (16#3E1#,16#3E0#,16#3E1#),(16#3E2#,16#3E2#,16#3E3#),(16#3E3#,16#3E2#,16#3E3#),
         (16#3E4#,16#3E4#,16#3E5#),(16#3E5#,16#3E4#,16#3E5#),(16#3E6#,16#3E6#,16#3E7#),
         (16#3E7#,16#3E6#,16#3E7#),(16#3E8#,16#3E8#,16#3E9#),(16#3E9#,16#3E8#,16#3E9#),
         (16#3EA#,16#3EA#,16#3EB#),(16#3EB#,16#3EA#,16#3EB#),(16#3EC#,16#3EC#,16#3ED#),
         (16#3ED#,16#3EC#,16#3ED#),(16#3EE#,16#3EE#,16#3EF#),(16#3EF#,16#3EE#,16#3EF#),
         (16#3F0#,16#39A#,16#3F0#),(16#3F1#,16#3A1#,16#3F1#),(16#3F2#,16#3F9#,16#3F2#),
         (16#3F3#,16#3F3#,16#3F3#),(16#3F4#,16#3F4#,16#3B8#),(16#3F5#,16#395#,16#3F5#),
         (16#3F7#,16#3F7#,16#3F8#),(16#3F8#,16#3F7#,16#3F8#),(16#3F9#,16#3F9#,16#3F2#),
         (16#3FA#,16#3FA#,16#3FB#),(16#3FB#,16#3FA#,16#3FB#),(16#3FC#,16#3FC#,16#3FC#),
         (16#3FD#,16#3FD#,16#37B#),(16#3FE#,16#3FE#,16#37C#),(16#3FF#,16#3FF#,16#37D#),
         (16#400#,16#400#,16#450#),(16#401#,16#401#,16#451#),(16#402#,16#402#,16#452#),
         (16#403#,16#403#,16#453#),(16#404#,16#404#,16#454#),(16#405#,16#405#,16#455#),
         (16#406#,16#406#,16#456#),(16#407#,16#407#,16#457#),(16#408#,16#408#,16#458#),
         (16#409#,16#409#,16#459#),(16#40A#,16#40A#,16#45A#),(16#40B#,16#40B#,16#45B#),
         (16#40C#,16#40C#,16#45C#),(16#40D#,16#40D#,16#45D#),(16#40E#,16#40E#,16#45E#),
         (16#40F#,16#40F#,16#45F#),(16#410#,16#410#,16#430#),(16#411#,16#411#,16#431#),
         (16#412#,16#412#,16#432#),(16#413#,16#413#,16#433#),(16#414#,16#414#,16#434#),
         (16#415#,16#415#,16#435#),(16#416#,16#416#,16#436#),(16#417#,16#417#,16#437#),
         (16#418#,16#418#,16#438#),(16#419#,16#419#,16#439#),(16#41A#,16#41A#,16#43A#),
         (16#41B#,16#41B#,16#43B#),(16#41C#,16#41C#,16#43C#),(16#41D#,16#41D#,16#43D#),
         (16#41E#,16#41E#,16#43E#),(16#41F#,16#41F#,16#43F#),(16#420#,16#420#,16#440#),
         (16#421#,16#421#,16#441#),(16#422#,16#422#,16#442#),(16#423#,16#423#,16#443#),
         (16#424#,16#424#,16#444#),(16#425#,16#425#,16#445#),(16#426#,16#426#,16#446#),
         (16#427#,16#427#,16#447#),(16#428#,16#428#,16#448#),(16#429#,16#429#,16#449#),
         (16#42A#,16#42A#,16#44A#),(16#42B#,16#42B#,16#44B#),(16#42C#,16#42C#,16#44C#),
         (16#42D#,16#42D#,16#44D#),(16#42E#,16#42E#,16#44E#),(16#42F#,16#42F#,16#44F#),
         (16#430#,16#410#,16#430#),(16#431#,16#411#,16#431#),(16#432#,16#412#,16#432#),
         (16#433#,16#413#,16#433#),(16#434#,16#414#,16#434#),(16#435#,16#415#,16#435#),
         (16#436#,16#416#,16#436#),(16#437#,16#417#,16#437#),(16#438#,16#418#,16#438#),
         (16#439#,16#419#,16#439#),(16#43A#,16#41A#,16#43A#),(16#43B#,16#41B#,16#43B#),
         (16#43C#,16#41C#,16#43C#),(16#43D#,16#41D#,16#43D#),(16#43E#,16#41E#,16#43E#),
         (16#43F#,16#41F#,16#43F#),(16#440#,16#420#,16#440#),(16#441#,16#421#,16#441#),
         (16#442#,16#422#,16#442#),(16#443#,16#423#,16#443#),(16#444#,16#424#,16#444#),
         (16#445#,16#425#,16#445#),(16#446#,16#426#,16#446#),(16#447#,16#427#,16#447#),
         (16#448#,16#428#,16#448#),(16#449#,16#429#,16#449#),(16#44A#,16#42A#,16#44A#),
         (16#44B#,16#42B#,16#44B#),(16#44C#,16#42C#,16#44C#),(16#44D#,16#42D#,16#44D#),
         (16#44E#,16#42E#,16#44E#),(16#44F#,16#42F#,16#44F#),(16#450#,16#400#,16#450#),
         (16#451#,16#401#,16#451#),(16#452#,16#402#,16#452#),(16#453#,16#403#,16#453#),
         (16#454#,16#404#,16#454#),(16#455#,16#405#,16#455#),(16#456#,16#406#,16#456#),
         (16#457#,16#407#,16#457#),(16#458#,16#408#,16#458#),(16#459#,16#409#,16#459#),
         (16#45A#,16#40A#,16#45A#),(16#45B#,16#40B#,16#45B#),(16#45C#,16#40C#,16#45C#),
         (16#45D#,16#40D#,16#45D#),(16#45E#,16#40E#,16#45E#),(16#45F#,16#40F#,16#45F#),
         (16#460#,16#460#,16#461#),(16#461#,16#460#,16#461#),(16#462#,16#462#,16#463#),
         (16#463#,16#462#,16#463#),(16#464#,16#464#,16#465#),(16#465#,16#464#,16#465#),
         (16#466#,16#466#,16#467#),(16#467#,16#466#,16#467#),(16#468#,16#468#,16#469#),
         (16#469#,16#468#,16#469#),(16#46A#,16#46A#,16#46B#),(16#46B#,16#46A#,16#46B#),
         (16#46C#,16#46C#,16#46D#),(16#46D#,16#46C#,16#46D#),(16#46E#,16#46E#,16#46F#),
         (16#46F#,16#46E#,16#46F#),(16#470#,16#470#,16#471#),(16#471#,16#470#,16#471#),
         (16#472#,16#472#,16#473#),(16#473#,16#472#,16#473#),(16#474#,16#474#,16#475#),
         (16#475#,16#474#,16#475#),(16#476#,16#476#,16#477#),(16#477#,16#476#,16#477#),
         (16#478#,16#478#,16#479#),(16#479#,16#478#,16#479#),(16#47A#,16#47A#,16#47B#),
         (16#47B#,16#47A#,16#47B#),(16#47C#,16#47C#,16#47D#),(16#47D#,16#47C#,16#47D#),
         (16#47E#,16#47E#,16#47F#),(16#47F#,16#47E#,16#47F#),(16#480#,16#480#,16#481#),
         (16#481#,16#480#,16#481#),(16#48A#,16#48A#,16#48B#),(16#48B#,16#48A#,16#48B#),
         (16#48C#,16#48C#,16#48D#),(16#48D#,16#48C#,16#48D#),(16#48E#,16#48E#,16#48F#),
         (16#48F#,16#48E#,16#48F#),(16#490#,16#490#,16#491#),(16#491#,16#490#,16#491#),
         (16#492#,16#492#,16#493#),(16#493#,16#492#,16#493#),(16#494#,16#494#,16#495#),
         (16#495#,16#494#,16#495#),(16#496#,16#496#,16#497#),(16#497#,16#496#,16#497#),
         (16#498#,16#498#,16#499#),(16#499#,16#498#,16#499#),(16#49A#,16#49A#,16#49B#),
         (16#49B#,16#49A#,16#49B#),(16#49C#,16#49C#,16#49D#),(16#49D#,16#49C#,16#49D#),
         (16#49E#,16#49E#,16#49F#),(16#49F#,16#49E#,16#49F#),(16#4A0#,16#4A0#,16#4A1#),
         (16#4A1#,16#4A0#,16#4A1#),(16#4A2#,16#4A2#,16#4A3#),(16#4A3#,16#4A2#,16#4A3#),
         (16#4A4#,16#4A4#,16#4A5#),(16#4A5#,16#4A4#,16#4A5#),(16#4A6#,16#4A6#,16#4A7#),
         (16#4A7#,16#4A6#,16#4A7#),(16#4A8#,16#4A8#,16#4A9#),(16#4A9#,16#4A8#,16#4A9#),
         (16#4AA#,16#4AA#,16#4AB#),(16#4AB#,16#4AA#,16#4AB#),(16#4AC#,16#4AC#,16#4AD#),
         (16#4AD#,16#4AC#,16#4AD#),(16#4AE#,16#4AE#,16#4AF#),(16#4AF#,16#4AE#,16#4AF#),
         (16#4B0#,16#4B0#,16#4B1#),(16#4B1#,16#4B0#,16#4B1#),(16#4B2#,16#4B2#,16#4B3#),
         (16#4B3#,16#4B2#,16#4B3#),(16#4B4#,16#4B4#,16#4B5#),(16#4B5#,16#4B4#,16#4B5#),
         (16#4B6#,16#4B6#,16#4B7#),(16#4B7#,16#4B6#,16#4B7#),(16#4B8#,16#4B8#,16#4B9#),
         (16#4B9#,16#4B8#,16#4B9#),(16#4BA#,16#4BA#,16#4BB#),(16#4BB#,16#4BA#,16#4BB#),
         (16#4BC#,16#4BC#,16#4BD#),(16#4BD#,16#4BC#,16#4BD#),(16#4BE#,16#4BE#,16#4BF#),
         (16#4BF#,16#4BE#,16#4BF#),(16#4C0#,16#4C0#,16#4CF#),(16#4C1#,16#4C1#,16#4C2#),
         (16#4C2#,16#4C1#,16#4C2#),(16#4C3#,16#4C3#,16#4C4#),(16#4C4#,16#4C3#,16#4C4#),
         (16#4C5#,16#4C5#,16#4C6#),(16#4C6#,16#4C5#,16#4C6#),(16#4C7#,16#4C7#,16#4C8#),
         (16#4C8#,16#4C7#,16#4C8#),(16#4C9#,16#4C9#,16#4CA#),(16#4CA#,16#4C9#,16#4CA#),
         (16#4CB#,16#4CB#,16#4CC#),(16#4CC#,16#4CB#,16#4CC#),(16#4CD#,16#4CD#,16#4CE#),
         (16#4CE#,16#4CD#,16#4CE#),(16#4CF#,16#4C0#,16#4CF#),(16#4D0#,16#4D0#,16#4D1#),
         (16#4D1#,16#4D0#,16#4D1#),(16#4D2#,16#4D2#,16#4D3#),(16#4D3#,16#4D2#,16#4D3#),
         (16#4D4#,16#4D4#,16#4D5#),(16#4D5#,16#4D4#,16#4D5#),(16#4D6#,16#4D6#,16#4D7#),
         (16#4D7#,16#4D6#,16#4D7#),(16#4D8#,16#4D8#,16#4D9#),(16#4D9#,16#4D8#,16#4D9#),
         (16#4DA#,16#4DA#,16#4DB#),(16#4DB#,16#4DA#,16#4DB#),(16#4DC#,16#4DC#,16#4DD#),
         (16#4DD#,16#4DC#,16#4DD#),(16#4DE#,16#4DE#,16#4DF#),(16#4DF#,16#4DE#,16#4DF#),
         (16#4E0#,16#4E0#,16#4E1#),(16#4E1#,16#4E0#,16#4E1#),(16#4E2#,16#4E2#,16#4E3#),
         (16#4E3#,16#4E2#,16#4E3#),(16#4E4#,16#4E4#,16#4E5#),(16#4E5#,16#4E4#,16#4E5#),
         (16#4E6#,16#4E6#,16#4E7#),(16#4E7#,16#4E6#,16#4E7#),(16#4E8#,16#4E8#,16#4E9#),
         (16#4E9#,16#4E8#,16#4E9#),(16#4EA#,16#4EA#,16#4EB#),(16#4EB#,16#4EA#,16#4EB#),
         (16#4EC#,16#4EC#,16#4ED#),(16#4ED#,16#4EC#,16#4ED#),(16#4EE#,16#4EE#,16#4EF#),
         (16#4EF#,16#4EE#,16#4EF#),(16#4F0#,16#4F0#,16#4F1#),(16#4F1#,16#4F0#,16#4F1#),
         (16#4F2#,16#4F2#,16#4F3#),(16#4F3#,16#4F2#,16#4F3#),(16#4F4#,16#4F4#,16#4F5#),
         (16#4F5#,16#4F4#,16#4F5#),(16#4F6#,16#4F6#,16#4F7#),(16#4F7#,16#4F6#,16#4F7#),
         (16#4F8#,16#4F8#,16#4F9#),(16#4F9#,16#4F8#,16#4F9#),(16#4FA#,16#4FA#,16#4FB#),
         (16#4FB#,16#4FA#,16#4FB#),(16#4FC#,16#4FC#,16#4FD#),(16#4FD#,16#4FC#,16#4FD#),
         (16#4FE#,16#4FE#,16#4FF#),(16#4FF#,16#4FE#,16#4FF#),(16#500#,16#500#,16#501#),
         (16#501#,16#500#,16#501#),(16#502#,16#502#,16#503#),(16#503#,16#502#,16#503#),
         (16#504#,16#504#,16#505#),(16#505#,16#504#,16#505#),(16#506#,16#506#,16#507#),
         (16#507#,16#506#,16#507#),(16#508#,16#508#,16#509#),(16#509#,16#508#,16#509#),
         (16#50A#,16#50A#,16#50B#),(16#50B#,16#50A#,16#50B#),(16#50C#,16#50C#,16#50D#),
         (16#50D#,16#50C#,16#50D#),(16#50E#,16#50E#,16#50F#),(16#50F#,16#50E#,16#50F#),
         (16#510#,16#510#,16#511#),(16#511#,16#510#,16#511#),(16#512#,16#512#,16#513#),
         (16#513#,16#512#,16#513#),(16#531#,16#531#,16#561#),(16#532#,16#532#,16#562#),
         (16#533#,16#533#,16#563#),(16#534#,16#534#,16#564#),(16#535#,16#535#,16#565#),
         (16#536#,16#536#,16#566#),(16#537#,16#537#,16#567#),(16#538#,16#538#,16#568#),
         (16#539#,16#539#,16#569#),(16#53A#,16#53A#,16#56A#),(16#53B#,16#53B#,16#56B#),
         (16#53C#,16#53C#,16#56C#),(16#53D#,16#53D#,16#56D#),(16#53E#,16#53E#,16#56E#),
         (16#53F#,16#53F#,16#56F#),(16#540#,16#540#,16#570#),(16#541#,16#541#,16#571#),
         (16#542#,16#542#,16#572#),(16#543#,16#543#,16#573#),(16#544#,16#544#,16#574#),
         (16#545#,16#545#,16#575#),(16#546#,16#546#,16#576#),(16#547#,16#547#,16#577#),
         (16#548#,16#548#,16#578#),(16#549#,16#549#,16#579#),(16#54A#,16#54A#,16#57A#),
         (16#54B#,16#54B#,16#57B#),(16#54C#,16#54C#,16#57C#),(16#54D#,16#54D#,16#57D#),
         (16#54E#,16#54E#,16#57E#),(16#54F#,16#54F#,16#57F#),(16#550#,16#550#,16#580#),
         (16#551#,16#551#,16#581#),(16#552#,16#552#,16#582#),(16#553#,16#553#,16#583#),
         (16#554#,16#554#,16#584#),(16#555#,16#555#,16#585#),(16#556#,16#556#,16#586#),
         (16#561#,16#531#,16#561#),(16#562#,16#532#,16#562#),(16#563#,16#533#,16#563#),
         (16#564#,16#534#,16#564#),(16#565#,16#535#,16#565#),(16#566#,16#536#,16#566#),
         (16#567#,16#537#,16#567#),(16#568#,16#538#,16#568#),(16#569#,16#539#,16#569#),
         (16#56A#,16#53A#,16#56A#),(16#56B#,16#53B#,16#56B#),(16#56C#,16#53C#,16#56C#),
         (16#56D#,16#53D#,16#56D#),(16#56E#,16#53E#,16#56E#),(16#56F#,16#53F#,16#56F#),
         (16#570#,16#540#,16#570#),(16#571#,16#541#,16#571#),(16#572#,16#542#,16#572#),
         (16#573#,16#543#,16#573#),(16#574#,16#544#,16#574#),(16#575#,16#545#,16#575#),
         (16#576#,16#546#,16#576#),(16#577#,16#547#,16#577#),(16#578#,16#548#,16#578#),
         (16#579#,16#549#,16#579#),(16#57A#,16#54A#,16#57A#),(16#57B#,16#54B#,16#57B#),
         (16#57C#,16#54C#,16#57C#),(16#57D#,16#54D#,16#57D#),(16#57E#,16#54E#,16#57E#),
         (16#57F#,16#54F#,16#57F#),(16#580#,16#550#,16#580#),(16#581#,16#551#,16#581#),
         (16#582#,16#552#,16#582#),(16#583#,16#553#,16#583#),(16#584#,16#554#,16#584#),
         (16#585#,16#555#,16#585#),(16#586#,16#556#,16#586#),(16#587#,16#587#,16#587#),
         (16#10A0#,16#10A0#,16#2D00#),(16#10A1#,16#10A1#,16#2D01#),(16#10A2#,16#10A2#,16#2D02#),
         (16#10A3#,16#10A3#,16#2D03#),(16#10A4#,16#10A4#,16#2D04#),(16#10A5#,16#10A5#,16#2D05#),
         (16#10A6#,16#10A6#,16#2D06#),(16#10A7#,16#10A7#,16#2D07#),(16#10A8#,16#10A8#,16#2D08#),
         (16#10A9#,16#10A9#,16#2D09#),(16#10AA#,16#10AA#,16#2D0A#),(16#10AB#,16#10AB#,16#2D0B#),
         (16#10AC#,16#10AC#,16#2D0C#),(16#10AD#,16#10AD#,16#2D0D#),(16#10AE#,16#10AE#,16#2D0E#),
         (16#10AF#,16#10AF#,16#2D0F#),(16#10B0#,16#10B0#,16#2D10#),(16#10B1#,16#10B1#,16#2D11#),
         (16#10B2#,16#10B2#,16#2D12#),(16#10B3#,16#10B3#,16#2D13#),(16#10B4#,16#10B4#,16#2D14#),
         (16#10B5#,16#10B5#,16#2D15#),(16#10B6#,16#10B6#,16#2D16#),(16#10B7#,16#10B7#,16#2D17#),
         (16#10B8#,16#10B8#,16#2D18#),(16#10B9#,16#10B9#,16#2D19#),(16#10BA#,16#10BA#,16#2D1A#),
         (16#10BB#,16#10BB#,16#2D1B#),(16#10BC#,16#10BC#,16#2D1C#),(16#10BD#,16#10BD#,16#2D1D#),
         (16#10BE#,16#10BE#,16#2D1E#),(16#10BF#,16#10BF#,16#2D1F#),(16#10C0#,16#10C0#,16#2D20#),
         (16#10C1#,16#10C1#,16#2D21#),(16#10C2#,16#10C2#,16#2D22#),(16#10C3#,16#10C3#,16#2D23#),
         (16#10C4#,16#10C4#,16#2D24#),(16#10C5#,16#10C5#,16#2D25#),(16#1D00#,16#1D00#,16#1D00#),
         (16#1D01#,16#1D01#,16#1D01#),(16#1D02#,16#1D02#,16#1D02#),(16#1D03#,16#1D03#,16#1D03#),
         (16#1D04#,16#1D04#,16#1D04#),(16#1D05#,16#1D05#,16#1D05#),(16#1D06#,16#1D06#,16#1D06#),
         (16#1D07#,16#1D07#,16#1D07#),(16#1D08#,16#1D08#,16#1D08#),(16#1D09#,16#1D09#,16#1D09#),
         (16#1D0A#,16#1D0A#,16#1D0A#),(16#1D0B#,16#1D0B#,16#1D0B#),(16#1D0C#,16#1D0C#,16#1D0C#),
         (16#1D0D#,16#1D0D#,16#1D0D#),(16#1D0E#,16#1D0E#,16#1D0E#),(16#1D0F#,16#1D0F#,16#1D0F#),
         (16#1D10#,16#1D10#,16#1D10#),(16#1D11#,16#1D11#,16#1D11#),(16#1D12#,16#1D12#,16#1D12#),
         (16#1D13#,16#1D13#,16#1D13#),(16#1D14#,16#1D14#,16#1D14#),(16#1D15#,16#1D15#,16#1D15#),
         (16#1D16#,16#1D16#,16#1D16#),(16#1D17#,16#1D17#,16#1D17#),(16#1D18#,16#1D18#,16#1D18#),
         (16#1D19#,16#1D19#,16#1D19#),(16#1D1A#,16#1D1A#,16#1D1A#),(16#1D1B#,16#1D1B#,16#1D1B#),
         (16#1D1C#,16#1D1C#,16#1D1C#),(16#1D1D#,16#1D1D#,16#1D1D#),(16#1D1E#,16#1D1E#,16#1D1E#),
         (16#1D1F#,16#1D1F#,16#1D1F#),(16#1D20#,16#1D20#,16#1D20#),(16#1D21#,16#1D21#,16#1D21#),
         (16#1D22#,16#1D22#,16#1D22#),(16#1D23#,16#1D23#,16#1D23#),(16#1D24#,16#1D24#,16#1D24#),
         (16#1D25#,16#1D25#,16#1D25#),(16#1D26#,16#1D26#,16#1D26#),(16#1D27#,16#1D27#,16#1D27#),
         (16#1D28#,16#1D28#,16#1D28#),(16#1D29#,16#1D29#,16#1D29#),(16#1D2A#,16#1D2A#,16#1D2A#),
         (16#1D2B#,16#1D2B#,16#1D2B#),(16#1D62#,16#1D62#,16#1D62#),(16#1D63#,16#1D63#,16#1D63#),
         (16#1D64#,16#1D64#,16#1D64#),(16#1D65#,16#1D65#,16#1D65#),(16#1D66#,16#1D66#,16#1D66#),
         (16#1D67#,16#1D67#,16#1D67#),(16#1D68#,16#1D68#,16#1D68#),(16#1D69#,16#1D69#,16#1D69#),
         (16#1D6A#,16#1D6A#,16#1D6A#),(16#1D6B#,16#1D6B#,16#1D6B#),(16#1D6C#,16#1D6C#,16#1D6C#),
         (16#1D6D#,16#1D6D#,16#1D6D#),(16#1D6E#,16#1D6E#,16#1D6E#),(16#1D6F#,16#1D6F#,16#1D6F#),
         (16#1D70#,16#1D70#,16#1D70#),(16#1D71#,16#1D71#,16#1D71#),(16#1D72#,16#1D72#,16#1D72#),
         (16#1D73#,16#1D73#,16#1D73#),(16#1D74#,16#1D74#,16#1D74#),(16#1D75#,16#1D75#,16#1D75#),
         (16#1D76#,16#1D76#,16#1D76#),(16#1D77#,16#1D77#,16#1D77#),(16#1D79#,16#1D79#,16#1D79#),
         (16#1D7A#,16#1D7A#,16#1D7A#),(16#1D7B#,16#1D7B#,16#1D7B#),(16#1D7C#,16#1D7C#,16#1D7C#),
         (16#1D7D#,16#2C63#,16#1D7D#),(16#1D7E#,16#1D7E#,16#1D7E#),(16#1D7F#,16#1D7F#,16#1D7F#),
         (16#1D80#,16#1D80#,16#1D80#),(16#1D81#,16#1D81#,16#1D81#),(16#1D82#,16#1D82#,16#1D82#),
         (16#1D83#,16#1D83#,16#1D83#),(16#1D84#,16#1D84#,16#1D84#),(16#1D85#,16#1D85#,16#1D85#),
         (16#1D86#,16#1D86#,16#1D86#),(16#1D87#,16#1D87#,16#1D87#),(16#1D88#,16#1D88#,16#1D88#),
         (16#1D89#,16#1D89#,16#1D89#),(16#1D8A#,16#1D8A#,16#1D8A#),(16#1D8B#,16#1D8B#,16#1D8B#),
         (16#1D8C#,16#1D8C#,16#1D8C#),(16#1D8D#,16#1D8D#,16#1D8D#),(16#1D8E#,16#1D8E#,16#1D8E#),
         (16#1D8F#,16#1D8F#,16#1D8F#),(16#1D90#,16#1D90#,16#1D90#),(16#1D91#,16#1D91#,16#1D91#),
         (16#1D92#,16#1D92#,16#1D92#),(16#1D93#,16#1D93#,16#1D93#),(16#1D94#,16#1D94#,16#1D94#),
         (16#1D95#,16#1D95#,16#1D95#),(16#1D96#,16#1D96#,16#1D96#),(16#1D97#,16#1D97#,16#1D97#),
         (16#1D98#,16#1D98#,16#1D98#),(16#1D99#,16#1D99#,16#1D99#),(16#1D9A#,16#1D9A#,16#1D9A#),
         (16#1E00#,16#1E00#,16#1E01#),(16#1E01#,16#1E00#,16#1E01#),(16#1E02#,16#1E02#,16#1E03#),
         (16#1E03#,16#1E02#,16#1E03#),(16#1E04#,16#1E04#,16#1E05#),(16#1E05#,16#1E04#,16#1E05#),
         (16#1E06#,16#1E06#,16#1E07#),(16#1E07#,16#1E06#,16#1E07#),(16#1E08#,16#1E08#,16#1E09#),
         (16#1E09#,16#1E08#,16#1E09#),(16#1E0A#,16#1E0A#,16#1E0B#),(16#1E0B#,16#1E0A#,16#1E0B#),
         (16#1E0C#,16#1E0C#,16#1E0D#),(16#1E0D#,16#1E0C#,16#1E0D#),(16#1E0E#,16#1E0E#,16#1E0F#),
         (16#1E0F#,16#1E0E#,16#1E0F#),(16#1E10#,16#1E10#,16#1E11#),(16#1E11#,16#1E10#,16#1E11#),
         (16#1E12#,16#1E12#,16#1E13#),(16#1E13#,16#1E12#,16#1E13#),(16#1E14#,16#1E14#,16#1E15#),
         (16#1E15#,16#1E14#,16#1E15#),(16#1E16#,16#1E16#,16#1E17#),(16#1E17#,16#1E16#,16#1E17#),
         (16#1E18#,16#1E18#,16#1E19#),(16#1E19#,16#1E18#,16#1E19#),(16#1E1A#,16#1E1A#,16#1E1B#),
         (16#1E1B#,16#1E1A#,16#1E1B#),(16#1E1C#,16#1E1C#,16#1E1D#),(16#1E1D#,16#1E1C#,16#1E1D#),
         (16#1E1E#,16#1E1E#,16#1E1F#),(16#1E1F#,16#1E1E#,16#1E1F#),(16#1E20#,16#1E20#,16#1E21#),
         (16#1E21#,16#1E20#,16#1E21#),(16#1E22#,16#1E22#,16#1E23#),(16#1E23#,16#1E22#,16#1E23#),
         (16#1E24#,16#1E24#,16#1E25#),(16#1E25#,16#1E24#,16#1E25#),(16#1E26#,16#1E26#,16#1E27#),
         (16#1E27#,16#1E26#,16#1E27#),(16#1E28#,16#1E28#,16#1E29#),(16#1E29#,16#1E28#,16#1E29#),
         (16#1E2A#,16#1E2A#,16#1E2B#),(16#1E2B#,16#1E2A#,16#1E2B#),(16#1E2C#,16#1E2C#,16#1E2D#),
         (16#1E2D#,16#1E2C#,16#1E2D#),(16#1E2E#,16#1E2E#,16#1E2F#),(16#1E2F#,16#1E2E#,16#1E2F#),
         (16#1E30#,16#1E30#,16#1E31#),(16#1E31#,16#1E30#,16#1E31#),(16#1E32#,16#1E32#,16#1E33#),
         (16#1E33#,16#1E32#,16#1E33#),(16#1E34#,16#1E34#,16#1E35#),(16#1E35#,16#1E34#,16#1E35#),
         (16#1E36#,16#1E36#,16#1E37#),(16#1E37#,16#1E36#,16#1E37#),(16#1E38#,16#1E38#,16#1E39#),
         (16#1E39#,16#1E38#,16#1E39#),(16#1E3A#,16#1E3A#,16#1E3B#),(16#1E3B#,16#1E3A#,16#1E3B#),
         (16#1E3C#,16#1E3C#,16#1E3D#),(16#1E3D#,16#1E3C#,16#1E3D#),(16#1E3E#,16#1E3E#,16#1E3F#),
         (16#1E3F#,16#1E3E#,16#1E3F#),(16#1E40#,16#1E40#,16#1E41#),(16#1E41#,16#1E40#,16#1E41#),
         (16#1E42#,16#1E42#,16#1E43#),(16#1E43#,16#1E42#,16#1E43#),(16#1E44#,16#1E44#,16#1E45#),
         (16#1E45#,16#1E44#,16#1E45#),(16#1E46#,16#1E46#,16#1E47#),(16#1E47#,16#1E46#,16#1E47#),
         (16#1E48#,16#1E48#,16#1E49#),(16#1E49#,16#1E48#,16#1E49#),(16#1E4A#,16#1E4A#,16#1E4B#),
         (16#1E4B#,16#1E4A#,16#1E4B#),(16#1E4C#,16#1E4C#,16#1E4D#),(16#1E4D#,16#1E4C#,16#1E4D#),
         (16#1E4E#,16#1E4E#,16#1E4F#),(16#1E4F#,16#1E4E#,16#1E4F#),(16#1E50#,16#1E50#,16#1E51#),
         (16#1E51#,16#1E50#,16#1E51#),(16#1E52#,16#1E52#,16#1E53#),(16#1E53#,16#1E52#,16#1E53#),
         (16#1E54#,16#1E54#,16#1E55#),(16#1E55#,16#1E54#,16#1E55#),(16#1E56#,16#1E56#,16#1E57#),
         (16#1E57#,16#1E56#,16#1E57#),(16#1E58#,16#1E58#,16#1E59#),(16#1E59#,16#1E58#,16#1E59#),
         (16#1E5A#,16#1E5A#,16#1E5B#),(16#1E5B#,16#1E5A#,16#1E5B#),(16#1E5C#,16#1E5C#,16#1E5D#),
         (16#1E5D#,16#1E5C#,16#1E5D#),(16#1E5E#,16#1E5E#,16#1E5F#),(16#1E5F#,16#1E5E#,16#1E5F#),
         (16#1E60#,16#1E60#,16#1E61#),(16#1E61#,16#1E60#,16#1E61#),(16#1E62#,16#1E62#,16#1E63#),
         (16#1E63#,16#1E62#,16#1E63#),(16#1E64#,16#1E64#,16#1E65#),(16#1E65#,16#1E64#,16#1E65#),
         (16#1E66#,16#1E66#,16#1E67#),(16#1E67#,16#1E66#,16#1E67#),(16#1E68#,16#1E68#,16#1E69#),
         (16#1E69#,16#1E68#,16#1E69#),(16#1E6A#,16#1E6A#,16#1E6B#),(16#1E6B#,16#1E6A#,16#1E6B#),
         (16#1E6C#,16#1E6C#,16#1E6D#),(16#1E6D#,16#1E6C#,16#1E6D#),(16#1E6E#,16#1E6E#,16#1E6F#),
         (16#1E6F#,16#1E6E#,16#1E6F#),(16#1E70#,16#1E70#,16#1E71#),(16#1E71#,16#1E70#,16#1E71#),
         (16#1E72#,16#1E72#,16#1E73#),(16#1E73#,16#1E72#,16#1E73#),(16#1E74#,16#1E74#,16#1E75#),
         (16#1E75#,16#1E74#,16#1E75#),(16#1E76#,16#1E76#,16#1E77#),(16#1E77#,16#1E76#,16#1E77#),
         (16#1E78#,16#1E78#,16#1E79#),(16#1E79#,16#1E78#,16#1E79#),(16#1E7A#,16#1E7A#,16#1E7B#),
         (16#1E7B#,16#1E7A#,16#1E7B#),(16#1E7C#,16#1E7C#,16#1E7D#),(16#1E7D#,16#1E7C#,16#1E7D#),
         (16#1E7E#,16#1E7E#,16#1E7F#),(16#1E7F#,16#1E7E#,16#1E7F#),(16#1E80#,16#1E80#,16#1E81#),
         (16#1E81#,16#1E80#,16#1E81#),(16#1E82#,16#1E82#,16#1E83#),(16#1E83#,16#1E82#,16#1E83#),
         (16#1E84#,16#1E84#,16#1E85#),(16#1E85#,16#1E84#,16#1E85#),(16#1E86#,16#1E86#,16#1E87#),
         (16#1E87#,16#1E86#,16#1E87#),(16#1E88#,16#1E88#,16#1E89#),(16#1E89#,16#1E88#,16#1E89#),
         (16#1E8A#,16#1E8A#,16#1E8B#),(16#1E8B#,16#1E8A#,16#1E8B#),(16#1E8C#,16#1E8C#,16#1E8D#),
         (16#1E8D#,16#1E8C#,16#1E8D#),(16#1E8E#,16#1E8E#,16#1E8F#),(16#1E8F#,16#1E8E#,16#1E8F#),
         (16#1E90#,16#1E90#,16#1E91#),(16#1E91#,16#1E90#,16#1E91#),(16#1E92#,16#1E92#,16#1E93#),
         (16#1E93#,16#1E92#,16#1E93#),(16#1E94#,16#1E94#,16#1E95#),(16#1E95#,16#1E94#,16#1E95#),
         (16#1E96#,16#1E96#,16#1E96#),(16#1E97#,16#1E97#,16#1E97#),(16#1E98#,16#1E98#,16#1E98#),
         (16#1E99#,16#1E99#,16#1E99#),(16#1E9A#,16#1E9A#,16#1E9A#),(16#1E9B#,16#1E60#,16#1E9B#),
         (16#1EA0#,16#1EA0#,16#1EA1#),(16#1EA1#,16#1EA0#,16#1EA1#),(16#1EA2#,16#1EA2#,16#1EA3#),
         (16#1EA3#,16#1EA2#,16#1EA3#),(16#1EA4#,16#1EA4#,16#1EA5#),(16#1EA5#,16#1EA4#,16#1EA5#),
         (16#1EA6#,16#1EA6#,16#1EA7#),(16#1EA7#,16#1EA6#,16#1EA7#),(16#1EA8#,16#1EA8#,16#1EA9#),
         (16#1EA9#,16#1EA8#,16#1EA9#),(16#1EAA#,16#1EAA#,16#1EAB#),(16#1EAB#,16#1EAA#,16#1EAB#),
         (16#1EAC#,16#1EAC#,16#1EAD#),(16#1EAD#,16#1EAC#,16#1EAD#),(16#1EAE#,16#1EAE#,16#1EAF#),
         (16#1EAF#,16#1EAE#,16#1EAF#),(16#1EB0#,16#1EB0#,16#1EB1#),(16#1EB1#,16#1EB0#,16#1EB1#),
         (16#1EB2#,16#1EB2#,16#1EB3#),(16#1EB3#,16#1EB2#,16#1EB3#),(16#1EB4#,16#1EB4#,16#1EB5#),
         (16#1EB5#,16#1EB4#,16#1EB5#),(16#1EB6#,16#1EB6#,16#1EB7#),(16#1EB7#,16#1EB6#,16#1EB7#),
         (16#1EB8#,16#1EB8#,16#1EB9#),(16#1EB9#,16#1EB8#,16#1EB9#),(16#1EBA#,16#1EBA#,16#1EBB#),
         (16#1EBB#,16#1EBA#,16#1EBB#),(16#1EBC#,16#1EBC#,16#1EBD#),(16#1EBD#,16#1EBC#,16#1EBD#),
         (16#1EBE#,16#1EBE#,16#1EBF#),(16#1EBF#,16#1EBE#,16#1EBF#),(16#1EC0#,16#1EC0#,16#1EC1#),
         (16#1EC1#,16#1EC0#,16#1EC1#),(16#1EC2#,16#1EC2#,16#1EC3#),(16#1EC3#,16#1EC2#,16#1EC3#),
         (16#1EC4#,16#1EC4#,16#1EC5#),(16#1EC5#,16#1EC4#,16#1EC5#),(16#1EC6#,16#1EC6#,16#1EC7#),
         (16#1EC7#,16#1EC6#,16#1EC7#),(16#1EC8#,16#1EC8#,16#1EC9#),(16#1EC9#,16#1EC8#,16#1EC9#),
         (16#1ECA#,16#1ECA#,16#1ECB#),(16#1ECB#,16#1ECA#,16#1ECB#),(16#1ECC#,16#1ECC#,16#1ECD#),
         (16#1ECD#,16#1ECC#,16#1ECD#),(16#1ECE#,16#1ECE#,16#1ECF#),(16#1ECF#,16#1ECE#,16#1ECF#),
         (16#1ED0#,16#1ED0#,16#1ED1#),(16#1ED1#,16#1ED0#,16#1ED1#),(16#1ED2#,16#1ED2#,16#1ED3#),
         (16#1ED3#,16#1ED2#,16#1ED3#),(16#1ED4#,16#1ED4#,16#1ED5#),(16#1ED5#,16#1ED4#,16#1ED5#),
         (16#1ED6#,16#1ED6#,16#1ED7#),(16#1ED7#,16#1ED6#,16#1ED7#),(16#1ED8#,16#1ED8#,16#1ED9#),
         (16#1ED9#,16#1ED8#,16#1ED9#),(16#1EDA#,16#1EDA#,16#1EDB#),(16#1EDB#,16#1EDA#,16#1EDB#),
         (16#1EDC#,16#1EDC#,16#1EDD#),(16#1EDD#,16#1EDC#,16#1EDD#),(16#1EDE#,16#1EDE#,16#1EDF#),
         (16#1EDF#,16#1EDE#,16#1EDF#),(16#1EE0#,16#1EE0#,16#1EE1#),(16#1EE1#,16#1EE0#,16#1EE1#),
         (16#1EE2#,16#1EE2#,16#1EE3#),(16#1EE3#,16#1EE2#,16#1EE3#),(16#1EE4#,16#1EE4#,16#1EE5#),
         (16#1EE5#,16#1EE4#,16#1EE5#),(16#1EE6#,16#1EE6#,16#1EE7#),(16#1EE7#,16#1EE6#,16#1EE7#),
         (16#1EE8#,16#1EE8#,16#1EE9#),(16#1EE9#,16#1EE8#,16#1EE9#),(16#1EEA#,16#1EEA#,16#1EEB#),
         (16#1EEB#,16#1EEA#,16#1EEB#),(16#1EEC#,16#1EEC#,16#1EED#),(16#1EED#,16#1EEC#,16#1EED#),
         (16#1EEE#,16#1EEE#,16#1EEF#),(16#1EEF#,16#1EEE#,16#1EEF#),(16#1EF0#,16#1EF0#,16#1EF1#),
         (16#1EF1#,16#1EF0#,16#1EF1#),(16#1EF2#,16#1EF2#,16#1EF3#),(16#1EF3#,16#1EF2#,16#1EF3#),
         (16#1EF4#,16#1EF4#,16#1EF5#),(16#1EF5#,16#1EF4#,16#1EF5#),(16#1EF6#,16#1EF6#,16#1EF7#),
         (16#1EF7#,16#1EF6#,16#1EF7#),(16#1EF8#,16#1EF8#,16#1EF9#),(16#1EF9#,16#1EF8#,16#1EF9#),
         (16#1F00#,16#1F08#,16#1F00#),(16#1F01#,16#1F09#,16#1F01#),(16#1F02#,16#1F0A#,16#1F02#),
         (16#1F03#,16#1F0B#,16#1F03#),(16#1F04#,16#1F0C#,16#1F04#),(16#1F05#,16#1F0D#,16#1F05#),
         (16#1F06#,16#1F0E#,16#1F06#),(16#1F07#,16#1F0F#,16#1F07#),(16#1F08#,16#1F08#,16#1F00#),
         (16#1F09#,16#1F09#,16#1F01#),(16#1F0A#,16#1F0A#,16#1F02#),(16#1F0B#,16#1F0B#,16#1F03#),
         (16#1F0C#,16#1F0C#,16#1F04#),(16#1F0D#,16#1F0D#,16#1F05#),(16#1F0E#,16#1F0E#,16#1F06#),
         (16#1F0F#,16#1F0F#,16#1F07#),(16#1F10#,16#1F18#,16#1F10#),(16#1F11#,16#1F19#,16#1F11#),
         (16#1F12#,16#1F1A#,16#1F12#),(16#1F13#,16#1F1B#,16#1F13#),(16#1F14#,16#1F1C#,16#1F14#),
         (16#1F15#,16#1F1D#,16#1F15#),(16#1F18#,16#1F18#,16#1F10#),(16#1F19#,16#1F19#,16#1F11#),
         (16#1F1A#,16#1F1A#,16#1F12#),(16#1F1B#,16#1F1B#,16#1F13#),(16#1F1C#,16#1F1C#,16#1F14#),
         (16#1F1D#,16#1F1D#,16#1F15#),(16#1F20#,16#1F28#,16#1F20#),(16#1F21#,16#1F29#,16#1F21#),
         (16#1F22#,16#1F2A#,16#1F22#),(16#1F23#,16#1F2B#,16#1F23#),(16#1F24#,16#1F2C#,16#1F24#),
         (16#1F25#,16#1F2D#,16#1F25#),(16#1F26#,16#1F2E#,16#1F26#),(16#1F27#,16#1F2F#,16#1F27#),
         (16#1F28#,16#1F28#,16#1F20#),(16#1F29#,16#1F29#,16#1F21#),(16#1F2A#,16#1F2A#,16#1F22#),
         (16#1F2B#,16#1F2B#,16#1F23#),(16#1F2C#,16#1F2C#,16#1F24#),(16#1F2D#,16#1F2D#,16#1F25#),
         (16#1F2E#,16#1F2E#,16#1F26#),(16#1F2F#,16#1F2F#,16#1F27#),(16#1F30#,16#1F38#,16#1F30#),
         (16#1F31#,16#1F39#,16#1F31#),(16#1F32#,16#1F3A#,16#1F32#),(16#1F33#,16#1F3B#,16#1F33#),
         (16#1F34#,16#1F3C#,16#1F34#),(16#1F35#,16#1F3D#,16#1F35#),(16#1F36#,16#1F3E#,16#1F36#),
         (16#1F37#,16#1F3F#,16#1F37#),(16#1F38#,16#1F38#,16#1F30#),(16#1F39#,16#1F39#,16#1F31#),
         (16#1F3A#,16#1F3A#,16#1F32#),(16#1F3B#,16#1F3B#,16#1F33#),(16#1F3C#,16#1F3C#,16#1F34#),
         (16#1F3D#,16#1F3D#,16#1F35#),(16#1F3E#,16#1F3E#,16#1F36#),(16#1F3F#,16#1F3F#,16#1F37#),
         (16#1F40#,16#1F48#,16#1F40#),(16#1F41#,16#1F49#,16#1F41#),(16#1F42#,16#1F4A#,16#1F42#),
         (16#1F43#,16#1F4B#,16#1F43#),(16#1F44#,16#1F4C#,16#1F44#),(16#1F45#,16#1F4D#,16#1F45#),
         (16#1F48#,16#1F48#,16#1F40#),(16#1F49#,16#1F49#,16#1F41#),(16#1F4A#,16#1F4A#,16#1F42#),
         (16#1F4B#,16#1F4B#,16#1F43#),(16#1F4C#,16#1F4C#,16#1F44#),(16#1F4D#,16#1F4D#,16#1F45#),
         (16#1F50#,16#1F50#,16#1F50#),(16#1F51#,16#1F59#,16#1F51#),(16#1F52#,16#1F52#,16#1F52#),
         (16#1F53#,16#1F5B#,16#1F53#),(16#1F54#,16#1F54#,16#1F54#),(16#1F55#,16#1F5D#,16#1F55#),
         (16#1F56#,16#1F56#,16#1F56#),(16#1F57#,16#1F5F#,16#1F57#),(16#1F59#,16#1F59#,16#1F51#),
         (16#1F5B#,16#1F5B#,16#1F53#),(16#1F5D#,16#1F5D#,16#1F55#),(16#1F5F#,16#1F5F#,16#1F57#),
         (16#1F60#,16#1F68#,16#1F60#),(16#1F61#,16#1F69#,16#1F61#),(16#1F62#,16#1F6A#,16#1F62#),
         (16#1F63#,16#1F6B#,16#1F63#),(16#1F64#,16#1F6C#,16#1F64#),(16#1F65#,16#1F6D#,16#1F65#),
         (16#1F66#,16#1F6E#,16#1F66#),(16#1F67#,16#1F6F#,16#1F67#),(16#1F68#,16#1F68#,16#1F60#),
         (16#1F69#,16#1F69#,16#1F61#),(16#1F6A#,16#1F6A#,16#1F62#),(16#1F6B#,16#1F6B#,16#1F63#),
         (16#1F6C#,16#1F6C#,16#1F64#),(16#1F6D#,16#1F6D#,16#1F65#),(16#1F6E#,16#1F6E#,16#1F66#),
         (16#1F6F#,16#1F6F#,16#1F67#),(16#1F70#,16#1FBA#,16#1F70#),(16#1F71#,16#1FBB#,16#1F71#),
         (16#1F72#,16#1FC8#,16#1F72#),(16#1F73#,16#1FC9#,16#1F73#),(16#1F74#,16#1FCA#,16#1F74#),
         (16#1F75#,16#1FCB#,16#1F75#),(16#1F76#,16#1FDA#,16#1F76#),(16#1F77#,16#1FDB#,16#1F77#),
         (16#1F78#,16#1FF8#,16#1F78#),(16#1F79#,16#1FF9#,16#1F79#),(16#1F7A#,16#1FEA#,16#1F7A#),
         (16#1F7B#,16#1FEB#,16#1F7B#),(16#1F7C#,16#1FFA#,16#1F7C#),(16#1F7D#,16#1FFB#,16#1F7D#),
         (16#1F80#,16#1F88#,16#1F80#),(16#1F81#,16#1F89#,16#1F81#),(16#1F82#,16#1F8A#,16#1F82#),
         (16#1F83#,16#1F8B#,16#1F83#),(16#1F84#,16#1F8C#,16#1F84#),(16#1F85#,16#1F8D#,16#1F85#),
         (16#1F86#,16#1F8E#,16#1F86#),(16#1F87#,16#1F8F#,16#1F87#),(16#1F88#,16#1F88#,16#1F80#),
         (16#1F89#,16#1F89#,16#1F81#),(16#1F8A#,16#1F8A#,16#1F82#),(16#1F8B#,16#1F8B#,16#1F83#),
         (16#1F8C#,16#1F8C#,16#1F84#),(16#1F8D#,16#1F8D#,16#1F85#),(16#1F8E#,16#1F8E#,16#1F86#),
         (16#1F8F#,16#1F8F#,16#1F87#),(16#1F90#,16#1F98#,16#1F90#),(16#1F91#,16#1F99#,16#1F91#),
         (16#1F92#,16#1F9A#,16#1F92#),(16#1F93#,16#1F9B#,16#1F93#),(16#1F94#,16#1F9C#,16#1F94#),
         (16#1F95#,16#1F9D#,16#1F95#),(16#1F96#,16#1F9E#,16#1F96#),(16#1F97#,16#1F9F#,16#1F97#),
         (16#1F98#,16#1F98#,16#1F90#),(16#1F99#,16#1F99#,16#1F91#),(16#1F9A#,16#1F9A#,16#1F92#),
         (16#1F9B#,16#1F9B#,16#1F93#),(16#1F9C#,16#1F9C#,16#1F94#),(16#1F9D#,16#1F9D#,16#1F95#),
         (16#1F9E#,16#1F9E#,16#1F96#),(16#1F9F#,16#1F9F#,16#1F97#),(16#1FA0#,16#1FA8#,16#1FA0#),
         (16#1FA1#,16#1FA9#,16#1FA1#),(16#1FA2#,16#1FAA#,16#1FA2#),(16#1FA3#,16#1FAB#,16#1FA3#),
         (16#1FA4#,16#1FAC#,16#1FA4#),(16#1FA5#,16#1FAD#,16#1FA5#),(16#1FA6#,16#1FAE#,16#1FA6#),
         (16#1FA7#,16#1FAF#,16#1FA7#),(16#1FA8#,16#1FA8#,16#1FA0#),(16#1FA9#,16#1FA9#,16#1FA1#),
         (16#1FAA#,16#1FAA#,16#1FA2#),(16#1FAB#,16#1FAB#,16#1FA3#),(16#1FAC#,16#1FAC#,16#1FA4#),
         (16#1FAD#,16#1FAD#,16#1FA5#),(16#1FAE#,16#1FAE#,16#1FA6#),(16#1FAF#,16#1FAF#,16#1FA7#),
         (16#1FB0#,16#1FB8#,16#1FB0#),(16#1FB1#,16#1FB9#,16#1FB1#),(16#1FB2#,16#1FB2#,16#1FB2#),
         (16#1FB3#,16#1FBC#,16#1FB3#),(16#1FB4#,16#1FB4#,16#1FB4#),(16#1FB6#,16#1FB6#,16#1FB6#),
         (16#1FB7#,16#1FB7#,16#1FB7#),(16#1FB8#,16#1FB8#,16#1FB0#),(16#1FB9#,16#1FB9#,16#1FB1#),
         (16#1FBA#,16#1FBA#,16#1F70#),(16#1FBB#,16#1FBB#,16#1F71#),(16#1FBC#,16#1FBC#,16#1FB3#),
         (16#1FBE#,16#399#,16#1FBE#),(16#1FC2#,16#1FC2#,16#1FC2#),(16#1FC3#,16#1FCC#,16#1FC3#),
         (16#1FC4#,16#1FC4#,16#1FC4#),(16#1FC6#,16#1FC6#,16#1FC6#),(16#1FC7#,16#1FC7#,16#1FC7#),
         (16#1FC8#,16#1FC8#,16#1F72#),(16#1FC9#,16#1FC9#,16#1F73#),(16#1FCA#,16#1FCA#,16#1F74#),
         (16#1FCB#,16#1FCB#,16#1F75#),(16#1FCC#,16#1FCC#,16#1FC3#),(16#1FD0#,16#1FD8#,16#1FD0#),
         (16#1FD1#,16#1FD9#,16#1FD1#),(16#1FD2#,16#1FD2#,16#1FD2#),(16#1FD3#,16#1FD3#,16#1FD3#),
         (16#1FD6#,16#1FD6#,16#1FD6#),(16#1FD7#,16#1FD7#,16#1FD7#),(16#1FD8#,16#1FD8#,16#1FD0#),
         (16#1FD9#,16#1FD9#,16#1FD1#),(16#1FDA#,16#1FDA#,16#1F76#),(16#1FDB#,16#1FDB#,16#1F77#),
         (16#1FE0#,16#1FE8#,16#1FE0#),(16#1FE1#,16#1FE9#,16#1FE1#),(16#1FE2#,16#1FE2#,16#1FE2#),
         (16#1FE3#,16#1FE3#,16#1FE3#),(16#1FE4#,16#1FE4#,16#1FE4#),(16#1FE5#,16#1FEC#,16#1FE5#),
         (16#1FE6#,16#1FE6#,16#1FE6#),(16#1FE7#,16#1FE7#,16#1FE7#),(16#1FE8#,16#1FE8#,16#1FE0#),
         (16#1FE9#,16#1FE9#,16#1FE1#),(16#1FEA#,16#1FEA#,16#1F7A#),(16#1FEB#,16#1FEB#,16#1F7B#),
         (16#1FEC#,16#1FEC#,16#1FE5#),(16#1FF2#,16#1FF2#,16#1FF2#),(16#1FF3#,16#1FFC#,16#1FF3#),
         (16#1FF4#,16#1FF4#,16#1FF4#),(16#1FF6#,16#1FF6#,16#1FF6#),(16#1FF7#,16#1FF7#,16#1FF7#),
         (16#1FF8#,16#1FF8#,16#1F78#),(16#1FF9#,16#1FF9#,16#1F79#),(16#1FFA#,16#1FFA#,16#1F7C#),
         (16#1FFB#,16#1FFB#,16#1F7D#),(16#1FFC#,16#1FFC#,16#1FF3#),(16#2071#,16#2071#,16#2071#),
         (16#207F#,16#207F#,16#207F#),(16#2102#,16#2102#,16#2102#),(16#2107#,16#2107#,16#2107#),
         (16#210A#,16#210A#,16#210A#),(16#210B#,16#210B#,16#210B#),(16#210C#,16#210C#,16#210C#),
         (16#210D#,16#210D#,16#210D#),(16#210E#,16#210E#,16#210E#),(16#210F#,16#210F#,16#210F#),
         (16#2110#,16#2110#,16#2110#),(16#2111#,16#2111#,16#2111#),(16#2112#,16#2112#,16#2112#),
         (16#2113#,16#2113#,16#2113#),(16#2115#,16#2115#,16#2115#),(16#2119#,16#2119#,16#2119#),
         (16#211A#,16#211A#,16#211A#),(16#211B#,16#211B#,16#211B#),(16#211C#,16#211C#,16#211C#),
         (16#211D#,16#211D#,16#211D#),(16#2124#,16#2124#,16#2124#),(16#2126#,16#2126#,16#3C9#),
         (16#2128#,16#2128#,16#2128#),(16#212A#,16#212A#,16#6B#),(16#212B#,16#212B#,16#E5#),
         (16#212C#,16#212C#,16#212C#),(16#212D#,16#212D#,16#212D#),(16#212F#,16#212F#,16#212F#),
         (16#2130#,16#2130#,16#2130#),(16#2131#,16#2131#,16#2131#),(16#2132#,16#2132#,16#214E#),
         (16#2133#,16#2133#,16#2133#),(16#2134#,16#2134#,16#2134#),(16#2139#,16#2139#,16#2139#),
         (16#213C#,16#213C#,16#213C#),(16#213D#,16#213D#,16#213D#),(16#213E#,16#213E#,16#213E#),
         (16#213F#,16#213F#,16#213F#),(16#2145#,16#2145#,16#2145#),(16#2146#,16#2146#,16#2146#),
         (16#2147#,16#2147#,16#2147#),(16#2148#,16#2148#,16#2148#),(16#2149#,16#2149#,16#2149#),
         (16#214E#,16#2132#,16#214E#),(16#2160#,16#2160#,16#2170#),(16#2161#,16#2161#,16#2171#),
         (16#2162#,16#2162#,16#2172#),(16#2163#,16#2163#,16#2173#),(16#2164#,16#2164#,16#2174#),
         (16#2165#,16#2165#,16#2175#),(16#2166#,16#2166#,16#2176#),(16#2167#,16#2167#,16#2177#),
         (16#2168#,16#2168#,16#2178#),(16#2169#,16#2169#,16#2179#),(16#216A#,16#216A#,16#217A#),
         (16#216B#,16#216B#,16#217B#),(16#216C#,16#216C#,16#217C#),(16#216D#,16#216D#,16#217D#),
         (16#216E#,16#216E#,16#217E#),(16#216F#,16#216F#,16#217F#),(16#2170#,16#2160#,16#2170#),
         (16#2171#,16#2161#,16#2171#),(16#2172#,16#2162#,16#2172#),(16#2173#,16#2163#,16#2173#),
         (16#2174#,16#2164#,16#2174#),(16#2175#,16#2165#,16#2175#),(16#2176#,16#2166#,16#2176#),
         (16#2177#,16#2167#,16#2177#),(16#2178#,16#2168#,16#2178#),(16#2179#,16#2169#,16#2179#),
         (16#217A#,16#216A#,16#217A#),(16#217B#,16#216B#,16#217B#),(16#217C#,16#216C#,16#217C#),
         (16#217D#,16#216D#,16#217D#),(16#217E#,16#216E#,16#217E#),(16#217F#,16#216F#,16#217F#),
         (16#2183#,16#2183#,16#2184#),(16#2184#,16#2183#,16#2184#),(16#24B6#,16#24B6#,16#24D0#),
         (16#24B7#,16#24B7#,16#24D1#),(16#24B8#,16#24B8#,16#24D2#),(16#24B9#,16#24B9#,16#24D3#),
         (16#24BA#,16#24BA#,16#24D4#),(16#24BB#,16#24BB#,16#24D5#),(16#24BC#,16#24BC#,16#24D6#),
         (16#24BD#,16#24BD#,16#24D7#),(16#24BE#,16#24BE#,16#24D8#),(16#24BF#,16#24BF#,16#24D9#),
         (16#24C0#,16#24C0#,16#24DA#),(16#24C1#,16#24C1#,16#24DB#),(16#24C2#,16#24C2#,16#24DC#),
         (16#24C3#,16#24C3#,16#24DD#),(16#24C4#,16#24C4#,16#24DE#),(16#24C5#,16#24C5#,16#24DF#),
         (16#24C6#,16#24C6#,16#24E0#),(16#24C7#,16#24C7#,16#24E1#),(16#24C8#,16#24C8#,16#24E2#),
         (16#24C9#,16#24C9#,16#24E3#),(16#24CA#,16#24CA#,16#24E4#),(16#24CB#,16#24CB#,16#24E5#),
         (16#24CC#,16#24CC#,16#24E6#),(16#24CD#,16#24CD#,16#24E7#),(16#24CE#,16#24CE#,16#24E8#),
         (16#24CF#,16#24CF#,16#24E9#),(16#24D0#,16#24B6#,16#24D0#),(16#24D1#,16#24B7#,16#24D1#),
         (16#24D2#,16#24B8#,16#24D2#),(16#24D3#,16#24B9#,16#24D3#),(16#24D4#,16#24BA#,16#24D4#),
         (16#24D5#,16#24BB#,16#24D5#),(16#24D6#,16#24BC#,16#24D6#),(16#24D7#,16#24BD#,16#24D7#),
         (16#24D8#,16#24BE#,16#24D8#),(16#24D9#,16#24BF#,16#24D9#),(16#24DA#,16#24C0#,16#24DA#),
         (16#24DB#,16#24C1#,16#24DB#),(16#24DC#,16#24C2#,16#24DC#),(16#24DD#,16#24C3#,16#24DD#),
         (16#24DE#,16#24C4#,16#24DE#),(16#24DF#,16#24C5#,16#24DF#),(16#24E0#,16#24C6#,16#24E0#),
         (16#24E1#,16#24C7#,16#24E1#),(16#24E2#,16#24C8#,16#24E2#),(16#24E3#,16#24C9#,16#24E3#),
         (16#24E4#,16#24CA#,16#24E4#),(16#24E5#,16#24CB#,16#24E5#),(16#24E6#,16#24CC#,16#24E6#),
         (16#24E7#,16#24CD#,16#24E7#),(16#24E8#,16#24CE#,16#24E8#),(16#24E9#,16#24CF#,16#24E9#),
         (16#2C00#,16#2C00#,16#2C30#),(16#2C01#,16#2C01#,16#2C31#),(16#2C02#,16#2C02#,16#2C32#),
         (16#2C03#,16#2C03#,16#2C33#),(16#2C04#,16#2C04#,16#2C34#),(16#2C05#,16#2C05#,16#2C35#),
         (16#2C06#,16#2C06#,16#2C36#),(16#2C07#,16#2C07#,16#2C37#),(16#2C08#,16#2C08#,16#2C38#),
         (16#2C09#,16#2C09#,16#2C39#),(16#2C0A#,16#2C0A#,16#2C3A#),(16#2C0B#,16#2C0B#,16#2C3B#),
         (16#2C0C#,16#2C0C#,16#2C3C#),(16#2C0D#,16#2C0D#,16#2C3D#),(16#2C0E#,16#2C0E#,16#2C3E#),
         (16#2C0F#,16#2C0F#,16#2C3F#),(16#2C10#,16#2C10#,16#2C40#),(16#2C11#,16#2C11#,16#2C41#),
         (16#2C12#,16#2C12#,16#2C42#),(16#2C13#,16#2C13#,16#2C43#),(16#2C14#,16#2C14#,16#2C44#),
         (16#2C15#,16#2C15#,16#2C45#),(16#2C16#,16#2C16#,16#2C46#),(16#2C17#,16#2C17#,16#2C47#),
         (16#2C18#,16#2C18#,16#2C48#),(16#2C19#,16#2C19#,16#2C49#),(16#2C1A#,16#2C1A#,16#2C4A#),
         (16#2C1B#,16#2C1B#,16#2C4B#),(16#2C1C#,16#2C1C#,16#2C4C#),(16#2C1D#,16#2C1D#,16#2C4D#),
         (16#2C1E#,16#2C1E#,16#2C4E#),(16#2C1F#,16#2C1F#,16#2C4F#),(16#2C20#,16#2C20#,16#2C50#),
         (16#2C21#,16#2C21#,16#2C51#),(16#2C22#,16#2C22#,16#2C52#),(16#2C23#,16#2C23#,16#2C53#),
         (16#2C24#,16#2C24#,16#2C54#),(16#2C25#,16#2C25#,16#2C55#),(16#2C26#,16#2C26#,16#2C56#),
         (16#2C27#,16#2C27#,16#2C57#),(16#2C28#,16#2C28#,16#2C58#),(16#2C29#,16#2C29#,16#2C59#),
         (16#2C2A#,16#2C2A#,16#2C5A#),(16#2C2B#,16#2C2B#,16#2C5B#),(16#2C2C#,16#2C2C#,16#2C5C#),
         (16#2C2D#,16#2C2D#,16#2C5D#),(16#2C2E#,16#2C2E#,16#2C5E#),(16#2C30#,16#2C00#,16#2C30#),
         (16#2C31#,16#2C01#,16#2C31#),(16#2C32#,16#2C02#,16#2C32#),(16#2C33#,16#2C03#,16#2C33#),
         (16#2C34#,16#2C04#,16#2C34#),(16#2C35#,16#2C05#,16#2C35#),(16#2C36#,16#2C06#,16#2C36#),
         (16#2C37#,16#2C07#,16#2C37#),(16#2C38#,16#2C08#,16#2C38#),(16#2C39#,16#2C09#,16#2C39#),
         (16#2C3A#,16#2C0A#,16#2C3A#),(16#2C3B#,16#2C0B#,16#2C3B#),(16#2C3C#,16#2C0C#,16#2C3C#),
         (16#2C3D#,16#2C0D#,16#2C3D#),(16#2C3E#,16#2C0E#,16#2C3E#),(16#2C3F#,16#2C0F#,16#2C3F#),
         (16#2C40#,16#2C10#,16#2C40#),(16#2C41#,16#2C11#,16#2C41#),(16#2C42#,16#2C12#,16#2C42#),
         (16#2C43#,16#2C13#,16#2C43#),(16#2C44#,16#2C14#,16#2C44#),(16#2C45#,16#2C15#,16#2C45#),
         (16#2C46#,16#2C16#,16#2C46#),(16#2C47#,16#2C17#,16#2C47#),(16#2C48#,16#2C18#,16#2C48#),
         (16#2C49#,16#2C19#,16#2C49#),(16#2C4A#,16#2C1A#,16#2C4A#),(16#2C4B#,16#2C1B#,16#2C4B#),
         (16#2C4C#,16#2C1C#,16#2C4C#),(16#2C4D#,16#2C1D#,16#2C4D#),(16#2C4E#,16#2C1E#,16#2C4E#),
         (16#2C4F#,16#2C1F#,16#2C4F#),(16#2C50#,16#2C20#,16#2C50#),(16#2C51#,16#2C21#,16#2C51#),
         (16#2C52#,16#2C22#,16#2C52#),(16#2C53#,16#2C23#,16#2C53#),(16#2C54#,16#2C24#,16#2C54#),
         (16#2C55#,16#2C25#,16#2C55#),(16#2C56#,16#2C26#,16#2C56#),(16#2C57#,16#2C27#,16#2C57#),
         (16#2C58#,16#2C28#,16#2C58#),(16#2C59#,16#2C29#,16#2C59#),(16#2C5A#,16#2C2A#,16#2C5A#),
         (16#2C5B#,16#2C2B#,16#2C5B#),(16#2C5C#,16#2C2C#,16#2C5C#),(16#2C5D#,16#2C2D#,16#2C5D#),
         (16#2C5E#,16#2C2E#,16#2C5E#),(16#2C60#,16#2C60#,16#2C61#),(16#2C61#,16#2C60#,16#2C61#),
         (16#2C62#,16#2C62#,16#26B#),(16#2C63#,16#2C63#,16#1D7D#),(16#2C64#,16#2C64#,16#27D#),
         (16#2C65#,16#23A#,16#2C65#),(16#2C66#,16#23E#,16#2C66#),(16#2C67#,16#2C67#,16#2C68#),
         (16#2C68#,16#2C67#,16#2C68#),(16#2C69#,16#2C69#,16#2C6A#),(16#2C6A#,16#2C69#,16#2C6A#),
         (16#2C6B#,16#2C6B#,16#2C6C#),(16#2C6C#,16#2C6B#,16#2C6C#),(16#2C74#,16#2C74#,16#2C74#),
         (16#2C75#,16#2C75#,16#2C76#),(16#2C76#,16#2C75#,16#2C76#),(16#2C77#,16#2C77#,16#2C77#),
         (16#2C80#,16#2C80#,16#2C81#),(16#2C81#,16#2C80#,16#2C81#),(16#2C82#,16#2C82#,16#2C83#),
         (16#2C83#,16#2C82#,16#2C83#),(16#2C84#,16#2C84#,16#2C85#),(16#2C85#,16#2C84#,16#2C85#),
         (16#2C86#,16#2C86#,16#2C87#),(16#2C87#,16#2C86#,16#2C87#),(16#2C88#,16#2C88#,16#2C89#),
         (16#2C89#,16#2C88#,16#2C89#),(16#2C8A#,16#2C8A#,16#2C8B#),(16#2C8B#,16#2C8A#,16#2C8B#),
         (16#2C8C#,16#2C8C#,16#2C8D#),(16#2C8D#,16#2C8C#,16#2C8D#),(16#2C8E#,16#2C8E#,16#2C8F#),
         (16#2C8F#,16#2C8E#,16#2C8F#),(16#2C90#,16#2C90#,16#2C91#),(16#2C91#,16#2C90#,16#2C91#),
         (16#2C92#,16#2C92#,16#2C93#),(16#2C93#,16#2C92#,16#2C93#),(16#2C94#,16#2C94#,16#2C95#),
         (16#2C95#,16#2C94#,16#2C95#),(16#2C96#,16#2C96#,16#2C97#),(16#2C97#,16#2C96#,16#2C97#),
         (16#2C98#,16#2C98#,16#2C99#),(16#2C99#,16#2C98#,16#2C99#),(16#2C9A#,16#2C9A#,16#2C9B#),
         (16#2C9B#,16#2C9A#,16#2C9B#),(16#2C9C#,16#2C9C#,16#2C9D#),(16#2C9D#,16#2C9C#,16#2C9D#),
         (16#2C9E#,16#2C9E#,16#2C9F#),(16#2C9F#,16#2C9E#,16#2C9F#),(16#2CA0#,16#2CA0#,16#2CA1#),
         (16#2CA1#,16#2CA0#,16#2CA1#),(16#2CA2#,16#2CA2#,16#2CA3#),(16#2CA3#,16#2CA2#,16#2CA3#),
         (16#2CA4#,16#2CA4#,16#2CA5#),(16#2CA5#,16#2CA4#,16#2CA5#),(16#2CA6#,16#2CA6#,16#2CA7#),
         (16#2CA7#,16#2CA6#,16#2CA7#),(16#2CA8#,16#2CA8#,16#2CA9#),(16#2CA9#,16#2CA8#,16#2CA9#),
         (16#2CAA#,16#2CAA#,16#2CAB#),(16#2CAB#,16#2CAA#,16#2CAB#),(16#2CAC#,16#2CAC#,16#2CAD#),
         (16#2CAD#,16#2CAC#,16#2CAD#),(16#2CAE#,16#2CAE#,16#2CAF#),(16#2CAF#,16#2CAE#,16#2CAF#),
         (16#2CB0#,16#2CB0#,16#2CB1#),(16#2CB1#,16#2CB0#,16#2CB1#),(16#2CB2#,16#2CB2#,16#2CB3#),
         (16#2CB3#,16#2CB2#,16#2CB3#),(16#2CB4#,16#2CB4#,16#2CB5#),(16#2CB5#,16#2CB4#,16#2CB5#),
         (16#2CB6#,16#2CB6#,16#2CB7#),(16#2CB7#,16#2CB6#,16#2CB7#),(16#2CB8#,16#2CB8#,16#2CB9#),
         (16#2CB9#,16#2CB8#,16#2CB9#),(16#2CBA#,16#2CBA#,16#2CBB#),(16#2CBB#,16#2CBA#,16#2CBB#),
         (16#2CBC#,16#2CBC#,16#2CBD#),(16#2CBD#,16#2CBC#,16#2CBD#),(16#2CBE#,16#2CBE#,16#2CBF#),
         (16#2CBF#,16#2CBE#,16#2CBF#),(16#2CC0#,16#2CC0#,16#2CC1#),(16#2CC1#,16#2CC0#,16#2CC1#),
         (16#2CC2#,16#2CC2#,16#2CC3#),(16#2CC3#,16#2CC2#,16#2CC3#),(16#2CC4#,16#2CC4#,16#2CC5#),
         (16#2CC5#,16#2CC4#,16#2CC5#),(16#2CC6#,16#2CC6#,16#2CC7#),(16#2CC7#,16#2CC6#,16#2CC7#),
         (16#2CC8#,16#2CC8#,16#2CC9#),(16#2CC9#,16#2CC8#,16#2CC9#),(16#2CCA#,16#2CCA#,16#2CCB#),
         (16#2CCB#,16#2CCA#,16#2CCB#),(16#2CCC#,16#2CCC#,16#2CCD#),(16#2CCD#,16#2CCC#,16#2CCD#),
         (16#2CCE#,16#2CCE#,16#2CCF#),(16#2CCF#,16#2CCE#,16#2CCF#),(16#2CD0#,16#2CD0#,16#2CD1#),
         (16#2CD1#,16#2CD0#,16#2CD1#),(16#2CD2#,16#2CD2#,16#2CD3#),(16#2CD3#,16#2CD2#,16#2CD3#),
         (16#2CD4#,16#2CD4#,16#2CD5#),(16#2CD5#,16#2CD4#,16#2CD5#),(16#2CD6#,16#2CD6#,16#2CD7#),
         (16#2CD7#,16#2CD6#,16#2CD7#),(16#2CD8#,16#2CD8#,16#2CD9#),(16#2CD9#,16#2CD8#,16#2CD9#),
         (16#2CDA#,16#2CDA#,16#2CDB#),(16#2CDB#,16#2CDA#,16#2CDB#),(16#2CDC#,16#2CDC#,16#2CDD#),
         (16#2CDD#,16#2CDC#,16#2CDD#),(16#2CDE#,16#2CDE#,16#2CDF#),(16#2CDF#,16#2CDE#,16#2CDF#),
         (16#2CE0#,16#2CE0#,16#2CE1#),(16#2CE1#,16#2CE0#,16#2CE1#),(16#2CE2#,16#2CE2#,16#2CE3#),
         (16#2CE3#,16#2CE2#,16#2CE3#),(16#2CE4#,16#2CE4#,16#2CE4#),(16#2D00#,16#10A0#,16#2D00#),
         (16#2D01#,16#10A1#,16#2D01#),(16#2D02#,16#10A2#,16#2D02#),(16#2D03#,16#10A3#,16#2D03#),
         (16#2D04#,16#10A4#,16#2D04#),(16#2D05#,16#10A5#,16#2D05#),(16#2D06#,16#10A6#,16#2D06#),
         (16#2D07#,16#10A7#,16#2D07#),(16#2D08#,16#10A8#,16#2D08#),(16#2D09#,16#10A9#,16#2D09#),
         (16#2D0A#,16#10AA#,16#2D0A#),(16#2D0B#,16#10AB#,16#2D0B#),(16#2D0C#,16#10AC#,16#2D0C#),
         (16#2D0D#,16#10AD#,16#2D0D#),(16#2D0E#,16#10AE#,16#2D0E#),(16#2D0F#,16#10AF#,16#2D0F#),
         (16#2D10#,16#10B0#,16#2D10#),(16#2D11#,16#10B1#,16#2D11#),(16#2D12#,16#10B2#,16#2D12#),
         (16#2D13#,16#10B3#,16#2D13#),(16#2D14#,16#10B4#,16#2D14#),(16#2D15#,16#10B5#,16#2D15#),
         (16#2D16#,16#10B6#,16#2D16#),(16#2D17#,16#10B7#,16#2D17#),(16#2D18#,16#10B8#,16#2D18#),
         (16#2D19#,16#10B9#,16#2D19#),(16#2D1A#,16#10BA#,16#2D1A#),(16#2D1B#,16#10BB#,16#2D1B#),
         (16#2D1C#,16#10BC#,16#2D1C#),(16#2D1D#,16#10BD#,16#2D1D#),(16#2D1E#,16#10BE#,16#2D1E#),
         (16#2D1F#,16#10BF#,16#2D1F#),(16#2D20#,16#10C0#,16#2D20#),(16#2D21#,16#10C1#,16#2D21#),
         (16#2D22#,16#10C2#,16#2D22#),(16#2D23#,16#10C3#,16#2D23#),(16#2D24#,16#10C4#,16#2D24#),
         (16#2D25#,16#10C5#,16#2D25#),(16#FB00#,16#FB00#,16#FB00#),(16#FB01#,16#FB01#,16#FB01#),
         (16#FB02#,16#FB02#,16#FB02#),(16#FB03#,16#FB03#,16#FB03#),(16#FB04#,16#FB04#,16#FB04#),
         (16#FB05#,16#FB05#,16#FB05#),(16#FB06#,16#FB06#,16#FB06#),(16#FB13#,16#FB13#,16#FB13#),
         (16#FB14#,16#FB14#,16#FB14#),(16#FB15#,16#FB15#,16#FB15#),(16#FB16#,16#FB16#,16#FB16#),
         (16#FB17#,16#FB17#,16#FB17#),(16#FF21#,16#FF21#,16#FF41#),(16#FF22#,16#FF22#,16#FF42#),
         (16#FF23#,16#FF23#,16#FF43#),(16#FF24#,16#FF24#,16#FF44#),(16#FF25#,16#FF25#,16#FF45#),
         (16#FF26#,16#FF26#,16#FF46#),(16#FF27#,16#FF27#,16#FF47#),(16#FF28#,16#FF28#,16#FF48#),
         (16#FF29#,16#FF29#,16#FF49#),(16#FF2A#,16#FF2A#,16#FF4A#),(16#FF2B#,16#FF2B#,16#FF4B#),
         (16#FF2C#,16#FF2C#,16#FF4C#),(16#FF2D#,16#FF2D#,16#FF4D#),(16#FF2E#,16#FF2E#,16#FF4E#),
         (16#FF2F#,16#FF2F#,16#FF4F#),(16#FF30#,16#FF30#,16#FF50#),(16#FF31#,16#FF31#,16#FF51#),
         (16#FF32#,16#FF32#,16#FF52#),(16#FF33#,16#FF33#,16#FF53#),(16#FF34#,16#FF34#,16#FF54#),
         (16#FF35#,16#FF35#,16#FF55#),(16#FF36#,16#FF36#,16#FF56#),(16#FF37#,16#FF37#,16#FF57#),
         (16#FF38#,16#FF38#,16#FF58#),(16#FF39#,16#FF39#,16#FF59#),(16#FF3A#,16#FF3A#,16#FF5A#),
         (16#FF41#,16#FF21#,16#FF41#),(16#FF42#,16#FF22#,16#FF42#),(16#FF43#,16#FF23#,16#FF43#),
         (16#FF44#,16#FF24#,16#FF44#),(16#FF45#,16#FF25#,16#FF45#),(16#FF46#,16#FF26#,16#FF46#),
         (16#FF47#,16#FF27#,16#FF47#),(16#FF48#,16#FF28#,16#FF48#),(16#FF49#,16#FF29#,16#FF49#),
         (16#FF4A#,16#FF2A#,16#FF4A#),(16#FF4B#,16#FF2B#,16#FF4B#),(16#FF4C#,16#FF2C#,16#FF4C#),
         (16#FF4D#,16#FF2D#,16#FF4D#),(16#FF4E#,16#FF2E#,16#FF4E#),(16#FF4F#,16#FF2F#,16#FF4F#),
         (16#FF50#,16#FF30#,16#FF50#),(16#FF51#,16#FF31#,16#FF51#),(16#FF52#,16#FF32#,16#FF52#),
         (16#FF53#,16#FF33#,16#FF53#),(16#FF54#,16#FF34#,16#FF54#),(16#FF55#,16#FF35#,16#FF55#),
         (16#FF56#,16#FF36#,16#FF56#),(16#FF57#,16#FF37#,16#FF57#),(16#FF58#,16#FF38#,16#FF58#),
         (16#FF59#,16#FF39#,16#FF59#),(16#FF5A#,16#FF3A#,16#FF5A#),(16#10400#,16#10400#,16#10428#),
         (16#10401#,16#10401#,16#10429#),(16#10402#,16#10402#,16#1042A#),(16#10403#,16#10403#,16#1042B#),
         (16#10404#,16#10404#,16#1042C#),(16#10405#,16#10405#,16#1042D#),(16#10406#,16#10406#,16#1042E#),
         (16#10407#,16#10407#,16#1042F#),(16#10408#,16#10408#,16#10430#),(16#10409#,16#10409#,16#10431#),
         (16#1040A#,16#1040A#,16#10432#),(16#1040B#,16#1040B#,16#10433#),(16#1040C#,16#1040C#,16#10434#),
         (16#1040D#,16#1040D#,16#10435#),(16#1040E#,16#1040E#,16#10436#),(16#1040F#,16#1040F#,16#10437#),
         (16#10410#,16#10410#,16#10438#),(16#10411#,16#10411#,16#10439#),(16#10412#,16#10412#,16#1043A#),
         (16#10413#,16#10413#,16#1043B#),(16#10414#,16#10414#,16#1043C#),(16#10415#,16#10415#,16#1043D#),
         (16#10416#,16#10416#,16#1043E#),(16#10417#,16#10417#,16#1043F#),(16#10418#,16#10418#,16#10440#),
         (16#10419#,16#10419#,16#10441#),(16#1041A#,16#1041A#,16#10442#),(16#1041B#,16#1041B#,16#10443#),
         (16#1041C#,16#1041C#,16#10444#),(16#1041D#,16#1041D#,16#10445#),(16#1041E#,16#1041E#,16#10446#),
         (16#1041F#,16#1041F#,16#10447#),(16#10420#,16#10420#,16#10448#),(16#10421#,16#10421#,16#10449#),
         (16#10422#,16#10422#,16#1044A#),(16#10423#,16#10423#,16#1044B#),(16#10424#,16#10424#,16#1044C#),
         (16#10425#,16#10425#,16#1044D#),(16#10426#,16#10426#,16#1044E#),(16#10427#,16#10427#,16#1044F#),
         (16#10428#,16#10400#,16#10428#),(16#10429#,16#10401#,16#10429#),(16#1042A#,16#10402#,16#1042A#),
         (16#1042B#,16#10403#,16#1042B#),(16#1042C#,16#10404#,16#1042C#),(16#1042D#,16#10405#,16#1042D#),
         (16#1042E#,16#10406#,16#1042E#),(16#1042F#,16#10407#,16#1042F#),(16#10430#,16#10408#,16#10430#),
         (16#10431#,16#10409#,16#10431#),(16#10432#,16#1040A#,16#10432#),(16#10433#,16#1040B#,16#10433#),
         (16#10434#,16#1040C#,16#10434#),(16#10435#,16#1040D#,16#10435#),(16#10436#,16#1040E#,16#10436#),
         (16#10437#,16#1040F#,16#10437#),(16#10438#,16#10410#,16#10438#),(16#10439#,16#10411#,16#10439#),
         (16#1043A#,16#10412#,16#1043A#),(16#1043B#,16#10413#,16#1043B#),(16#1043C#,16#10414#,16#1043C#),
         (16#1043D#,16#10415#,16#1043D#),(16#1043E#,16#10416#,16#1043E#),(16#1043F#,16#10417#,16#1043F#),
         (16#10440#,16#10418#,16#10440#),(16#10441#,16#10419#,16#10441#),(16#10442#,16#1041A#,16#10442#),
         (16#10443#,16#1041B#,16#10443#),(16#10444#,16#1041C#,16#10444#),(16#10445#,16#1041D#,16#10445#),
         (16#10446#,16#1041E#,16#10446#),(16#10447#,16#1041F#,16#10447#),(16#10448#,16#10420#,16#10448#),
         (16#10449#,16#10421#,16#10449#),(16#1044A#,16#10422#,16#1044A#),(16#1044B#,16#10423#,16#1044B#),
         (16#1044C#,16#10424#,16#1044C#),(16#1044D#,16#10425#,16#1044D#),(16#1044E#,16#10426#,16#1044E#),
         (16#1044F#,16#10427#,16#1044F#),(16#1D400#,16#1D400#,16#1D400#),(16#1D401#,16#1D401#,16#1D401#),
         (16#1D402#,16#1D402#,16#1D402#),(16#1D403#,16#1D403#,16#1D403#),(16#1D404#,16#1D404#,16#1D404#),
         (16#1D405#,16#1D405#,16#1D405#),(16#1D406#,16#1D406#,16#1D406#),(16#1D407#,16#1D407#,16#1D407#),
         (16#1D408#,16#1D408#,16#1D408#),(16#1D409#,16#1D409#,16#1D409#),(16#1D40A#,16#1D40A#,16#1D40A#),
         (16#1D40B#,16#1D40B#,16#1D40B#),(16#1D40C#,16#1D40C#,16#1D40C#),(16#1D40D#,16#1D40D#,16#1D40D#),
         (16#1D40E#,16#1D40E#,16#1D40E#),(16#1D40F#,16#1D40F#,16#1D40F#),(16#1D410#,16#1D410#,16#1D410#),
         (16#1D411#,16#1D411#,16#1D411#),(16#1D412#,16#1D412#,16#1D412#),(16#1D413#,16#1D413#,16#1D413#),
         (16#1D414#,16#1D414#,16#1D414#),(16#1D415#,16#1D415#,16#1D415#),(16#1D416#,16#1D416#,16#1D416#),
         (16#1D417#,16#1D417#,16#1D417#),(16#1D418#,16#1D418#,16#1D418#),(16#1D419#,16#1D419#,16#1D419#),
         (16#1D41A#,16#1D41A#,16#1D41A#),(16#1D41B#,16#1D41B#,16#1D41B#),(16#1D41C#,16#1D41C#,16#1D41C#),
         (16#1D41D#,16#1D41D#,16#1D41D#),(16#1D41E#,16#1D41E#,16#1D41E#),(16#1D41F#,16#1D41F#,16#1D41F#),
         (16#1D420#,16#1D420#,16#1D420#),(16#1D421#,16#1D421#,16#1D421#),(16#1D422#,16#1D422#,16#1D422#),
         (16#1D423#,16#1D423#,16#1D423#),(16#1D424#,16#1D424#,16#1D424#),(16#1D425#,16#1D425#,16#1D425#),
         (16#1D426#,16#1D426#,16#1D426#),(16#1D427#,16#1D427#,16#1D427#),(16#1D428#,16#1D428#,16#1D428#),
         (16#1D429#,16#1D429#,16#1D429#),(16#1D42A#,16#1D42A#,16#1D42A#),(16#1D42B#,16#1D42B#,16#1D42B#),
         (16#1D42C#,16#1D42C#,16#1D42C#),(16#1D42D#,16#1D42D#,16#1D42D#),(16#1D42E#,16#1D42E#,16#1D42E#),
         (16#1D42F#,16#1D42F#,16#1D42F#),(16#1D430#,16#1D430#,16#1D430#),(16#1D431#,16#1D431#,16#1D431#),
         (16#1D432#,16#1D432#,16#1D432#),(16#1D433#,16#1D433#,16#1D433#),(16#1D434#,16#1D434#,16#1D434#),
         (16#1D435#,16#1D435#,16#1D435#),(16#1D436#,16#1D436#,16#1D436#),(16#1D437#,16#1D437#,16#1D437#),
         (16#1D438#,16#1D438#,16#1D438#),(16#1D439#,16#1D439#,16#1D439#),(16#1D43A#,16#1D43A#,16#1D43A#),
         (16#1D43B#,16#1D43B#,16#1D43B#),(16#1D43C#,16#1D43C#,16#1D43C#),(16#1D43D#,16#1D43D#,16#1D43D#),
         (16#1D43E#,16#1D43E#,16#1D43E#),(16#1D43F#,16#1D43F#,16#1D43F#),(16#1D440#,16#1D440#,16#1D440#),
         (16#1D441#,16#1D441#,16#1D441#),(16#1D442#,16#1D442#,16#1D442#),(16#1D443#,16#1D443#,16#1D443#),
         (16#1D444#,16#1D444#,16#1D444#),(16#1D445#,16#1D445#,16#1D445#),(16#1D446#,16#1D446#,16#1D446#),
         (16#1D447#,16#1D447#,16#1D447#),(16#1D448#,16#1D448#,16#1D448#),(16#1D449#,16#1D449#,16#1D449#),
         (16#1D44A#,16#1D44A#,16#1D44A#),(16#1D44B#,16#1D44B#,16#1D44B#),(16#1D44C#,16#1D44C#,16#1D44C#),
         (16#1D44D#,16#1D44D#,16#1D44D#),(16#1D44E#,16#1D44E#,16#1D44E#),(16#1D44F#,16#1D44F#,16#1D44F#),
         (16#1D450#,16#1D450#,16#1D450#),(16#1D451#,16#1D451#,16#1D451#),(16#1D452#,16#1D452#,16#1D452#),
         (16#1D453#,16#1D453#,16#1D453#),(16#1D454#,16#1D454#,16#1D454#),(16#1D456#,16#1D456#,16#1D456#),
         (16#1D457#,16#1D457#,16#1D457#),(16#1D458#,16#1D458#,16#1D458#),(16#1D459#,16#1D459#,16#1D459#),
         (16#1D45A#,16#1D45A#,16#1D45A#),(16#1D45B#,16#1D45B#,16#1D45B#),(16#1D45C#,16#1D45C#,16#1D45C#),
         (16#1D45D#,16#1D45D#,16#1D45D#),(16#1D45E#,16#1D45E#,16#1D45E#),(16#1D45F#,16#1D45F#,16#1D45F#),
         (16#1D460#,16#1D460#,16#1D460#),(16#1D461#,16#1D461#,16#1D461#),(16#1D462#,16#1D462#,16#1D462#),
         (16#1D463#,16#1D463#,16#1D463#),(16#1D464#,16#1D464#,16#1D464#),(16#1D465#,16#1D465#,16#1D465#),
         (16#1D466#,16#1D466#,16#1D466#),(16#1D467#,16#1D467#,16#1D467#),(16#1D468#,16#1D468#,16#1D468#),
         (16#1D469#,16#1D469#,16#1D469#),(16#1D46A#,16#1D46A#,16#1D46A#),(16#1D46B#,16#1D46B#,16#1D46B#),
         (16#1D46C#,16#1D46C#,16#1D46C#),(16#1D46D#,16#1D46D#,16#1D46D#),(16#1D46E#,16#1D46E#,16#1D46E#),
         (16#1D46F#,16#1D46F#,16#1D46F#),(16#1D470#,16#1D470#,16#1D470#),(16#1D471#,16#1D471#,16#1D471#),
         (16#1D472#,16#1D472#,16#1D472#),(16#1D473#,16#1D473#,16#1D473#),(16#1D474#,16#1D474#,16#1D474#),
         (16#1D475#,16#1D475#,16#1D475#),(16#1D476#,16#1D476#,16#1D476#),(16#1D477#,16#1D477#,16#1D477#),
         (16#1D478#,16#1D478#,16#1D478#),(16#1D479#,16#1D479#,16#1D479#),(16#1D47A#,16#1D47A#,16#1D47A#),
         (16#1D47B#,16#1D47B#,16#1D47B#),(16#1D47C#,16#1D47C#,16#1D47C#),(16#1D47D#,16#1D47D#,16#1D47D#),
         (16#1D47E#,16#1D47E#,16#1D47E#),(16#1D47F#,16#1D47F#,16#1D47F#),(16#1D480#,16#1D480#,16#1D480#),
         (16#1D481#,16#1D481#,16#1D481#),(16#1D482#,16#1D482#,16#1D482#),(16#1D483#,16#1D483#,16#1D483#),
         (16#1D484#,16#1D484#,16#1D484#),(16#1D485#,16#1D485#,16#1D485#),(16#1D486#,16#1D486#,16#1D486#),
         (16#1D487#,16#1D487#,16#1D487#),(16#1D488#,16#1D488#,16#1D488#),(16#1D489#,16#1D489#,16#1D489#),
         (16#1D48A#,16#1D48A#,16#1D48A#),(16#1D48B#,16#1D48B#,16#1D48B#),(16#1D48C#,16#1D48C#,16#1D48C#),
         (16#1D48D#,16#1D48D#,16#1D48D#),(16#1D48E#,16#1D48E#,16#1D48E#),(16#1D48F#,16#1D48F#,16#1D48F#),
         (16#1D490#,16#1D490#,16#1D490#),(16#1D491#,16#1D491#,16#1D491#),(16#1D492#,16#1D492#,16#1D492#),
         (16#1D493#,16#1D493#,16#1D493#),(16#1D494#,16#1D494#,16#1D494#),(16#1D495#,16#1D495#,16#1D495#),
         (16#1D496#,16#1D496#,16#1D496#),(16#1D497#,16#1D497#,16#1D497#),(16#1D498#,16#1D498#,16#1D498#),
         (16#1D499#,16#1D499#,16#1D499#),(16#1D49A#,16#1D49A#,16#1D49A#),(16#1D49B#,16#1D49B#,16#1D49B#),
         (16#1D49C#,16#1D49C#,16#1D49C#),(16#1D49E#,16#1D49E#,16#1D49E#),(16#1D49F#,16#1D49F#,16#1D49F#),
         (16#1D4A2#,16#1D4A2#,16#1D4A2#),(16#1D4A5#,16#1D4A5#,16#1D4A5#),(16#1D4A6#,16#1D4A6#,16#1D4A6#),
         (16#1D4A9#,16#1D4A9#,16#1D4A9#),(16#1D4AA#,16#1D4AA#,16#1D4AA#),(16#1D4AB#,16#1D4AB#,16#1D4AB#),
         (16#1D4AC#,16#1D4AC#,16#1D4AC#),(16#1D4AE#,16#1D4AE#,16#1D4AE#),(16#1D4AF#,16#1D4AF#,16#1D4AF#),
         (16#1D4B0#,16#1D4B0#,16#1D4B0#),(16#1D4B1#,16#1D4B1#,16#1D4B1#),(16#1D4B2#,16#1D4B2#,16#1D4B2#),
         (16#1D4B3#,16#1D4B3#,16#1D4B3#),(16#1D4B4#,16#1D4B4#,16#1D4B4#),(16#1D4B5#,16#1D4B5#,16#1D4B5#),
         (16#1D4B6#,16#1D4B6#,16#1D4B6#),(16#1D4B7#,16#1D4B7#,16#1D4B7#),(16#1D4B8#,16#1D4B8#,16#1D4B8#),
         (16#1D4B9#,16#1D4B9#,16#1D4B9#),(16#1D4BB#,16#1D4BB#,16#1D4BB#),(16#1D4BD#,16#1D4BD#,16#1D4BD#),
         (16#1D4BE#,16#1D4BE#,16#1D4BE#),(16#1D4BF#,16#1D4BF#,16#1D4BF#),(16#1D4C0#,16#1D4C0#,16#1D4C0#),
         (16#1D4C1#,16#1D4C1#,16#1D4C1#),(16#1D4C2#,16#1D4C2#,16#1D4C2#),(16#1D4C3#,16#1D4C3#,16#1D4C3#),
         (16#1D4C5#,16#1D4C5#,16#1D4C5#),(16#1D4C6#,16#1D4C6#,16#1D4C6#),(16#1D4C7#,16#1D4C7#,16#1D4C7#),
         (16#1D4C8#,16#1D4C8#,16#1D4C8#),(16#1D4C9#,16#1D4C9#,16#1D4C9#),(16#1D4CA#,16#1D4CA#,16#1D4CA#),
         (16#1D4CB#,16#1D4CB#,16#1D4CB#),(16#1D4CC#,16#1D4CC#,16#1D4CC#),(16#1D4CD#,16#1D4CD#,16#1D4CD#),
         (16#1D4CE#,16#1D4CE#,16#1D4CE#),(16#1D4CF#,16#1D4CF#,16#1D4CF#),(16#1D4D0#,16#1D4D0#,16#1D4D0#),
         (16#1D4D1#,16#1D4D1#,16#1D4D1#),(16#1D4D2#,16#1D4D2#,16#1D4D2#),(16#1D4D3#,16#1D4D3#,16#1D4D3#),
         (16#1D4D4#,16#1D4D4#,16#1D4D4#),(16#1D4D5#,16#1D4D5#,16#1D4D5#),(16#1D4D6#,16#1D4D6#,16#1D4D6#),
         (16#1D4D7#,16#1D4D7#,16#1D4D7#),(16#1D4D8#,16#1D4D8#,16#1D4D8#),(16#1D4D9#,16#1D4D9#,16#1D4D9#),
         (16#1D4DA#,16#1D4DA#,16#1D4DA#),(16#1D4DB#,16#1D4DB#,16#1D4DB#),(16#1D4DC#,16#1D4DC#,16#1D4DC#),
         (16#1D4DD#,16#1D4DD#,16#1D4DD#),(16#1D4DE#,16#1D4DE#,16#1D4DE#),(16#1D4DF#,16#1D4DF#,16#1D4DF#),
         (16#1D4E0#,16#1D4E0#,16#1D4E0#),(16#1D4E1#,16#1D4E1#,16#1D4E1#),(16#1D4E2#,16#1D4E2#,16#1D4E2#),
         (16#1D4E3#,16#1D4E3#,16#1D4E3#),(16#1D4E4#,16#1D4E4#,16#1D4E4#),(16#1D4E5#,16#1D4E5#,16#1D4E5#),
         (16#1D4E6#,16#1D4E6#,16#1D4E6#),(16#1D4E7#,16#1D4E7#,16#1D4E7#),(16#1D4E8#,16#1D4E8#,16#1D4E8#),
         (16#1D4E9#,16#1D4E9#,16#1D4E9#),(16#1D4EA#,16#1D4EA#,16#1D4EA#),(16#1D4EB#,16#1D4EB#,16#1D4EB#),
         (16#1D4EC#,16#1D4EC#,16#1D4EC#),(16#1D4ED#,16#1D4ED#,16#1D4ED#),(16#1D4EE#,16#1D4EE#,16#1D4EE#),
         (16#1D4EF#,16#1D4EF#,16#1D4EF#),(16#1D4F0#,16#1D4F0#,16#1D4F0#),(16#1D4F1#,16#1D4F1#,16#1D4F1#),
         (16#1D4F2#,16#1D4F2#,16#1D4F2#),(16#1D4F3#,16#1D4F3#,16#1D4F3#),(16#1D4F4#,16#1D4F4#,16#1D4F4#),
         (16#1D4F5#,16#1D4F5#,16#1D4F5#),(16#1D4F6#,16#1D4F6#,16#1D4F6#),(16#1D4F7#,16#1D4F7#,16#1D4F7#),
         (16#1D4F8#,16#1D4F8#,16#1D4F8#),(16#1D4F9#,16#1D4F9#,16#1D4F9#),(16#1D4FA#,16#1D4FA#,16#1D4FA#),
         (16#1D4FB#,16#1D4FB#,16#1D4FB#),(16#1D4FC#,16#1D4FC#,16#1D4FC#),(16#1D4FD#,16#1D4FD#,16#1D4FD#),
         (16#1D4FE#,16#1D4FE#,16#1D4FE#),(16#1D4FF#,16#1D4FF#,16#1D4FF#),(16#1D500#,16#1D500#,16#1D500#),
         (16#1D501#,16#1D501#,16#1D501#),(16#1D502#,16#1D502#,16#1D502#),(16#1D503#,16#1D503#,16#1D503#),
         (16#1D504#,16#1D504#,16#1D504#),(16#1D505#,16#1D505#,16#1D505#),(16#1D507#,16#1D507#,16#1D507#),
         (16#1D508#,16#1D508#,16#1D508#),(16#1D509#,16#1D509#,16#1D509#),(16#1D50A#,16#1D50A#,16#1D50A#),
         (16#1D50D#,16#1D50D#,16#1D50D#),(16#1D50E#,16#1D50E#,16#1D50E#),(16#1D50F#,16#1D50F#,16#1D50F#),
         (16#1D510#,16#1D510#,16#1D510#),(16#1D511#,16#1D511#,16#1D511#),(16#1D512#,16#1D512#,16#1D512#),
         (16#1D513#,16#1D513#,16#1D513#),(16#1D514#,16#1D514#,16#1D514#),(16#1D516#,16#1D516#,16#1D516#),
         (16#1D517#,16#1D517#,16#1D517#),(16#1D518#,16#1D518#,16#1D518#),(16#1D519#,16#1D519#,16#1D519#),
         (16#1D51A#,16#1D51A#,16#1D51A#),(16#1D51B#,16#1D51B#,16#1D51B#),(16#1D51C#,16#1D51C#,16#1D51C#),
         (16#1D51E#,16#1D51E#,16#1D51E#),(16#1D51F#,16#1D51F#,16#1D51F#),(16#1D520#,16#1D520#,16#1D520#),
         (16#1D521#,16#1D521#,16#1D521#),(16#1D522#,16#1D522#,16#1D522#),(16#1D523#,16#1D523#,16#1D523#),
         (16#1D524#,16#1D524#,16#1D524#),(16#1D525#,16#1D525#,16#1D525#),(16#1D526#,16#1D526#,16#1D526#),
         (16#1D527#,16#1D527#,16#1D527#),(16#1D528#,16#1D528#,16#1D528#),(16#1D529#,16#1D529#,16#1D529#),
         (16#1D52A#,16#1D52A#,16#1D52A#),(16#1D52B#,16#1D52B#,16#1D52B#),(16#1D52C#,16#1D52C#,16#1D52C#),
         (16#1D52D#,16#1D52D#,16#1D52D#),(16#1D52E#,16#1D52E#,16#1D52E#),(16#1D52F#,16#1D52F#,16#1D52F#),
         (16#1D530#,16#1D530#,16#1D530#),(16#1D531#,16#1D531#,16#1D531#),(16#1D532#,16#1D532#,16#1D532#),
         (16#1D533#,16#1D533#,16#1D533#),(16#1D534#,16#1D534#,16#1D534#),(16#1D535#,16#1D535#,16#1D535#),
         (16#1D536#,16#1D536#,16#1D536#),(16#1D537#,16#1D537#,16#1D537#),(16#1D538#,16#1D538#,16#1D538#),
         (16#1D539#,16#1D539#,16#1D539#),(16#1D53B#,16#1D53B#,16#1D53B#),(16#1D53C#,16#1D53C#,16#1D53C#),
         (16#1D53D#,16#1D53D#,16#1D53D#),(16#1D53E#,16#1D53E#,16#1D53E#),(16#1D540#,16#1D540#,16#1D540#),
         (16#1D541#,16#1D541#,16#1D541#),(16#1D542#,16#1D542#,16#1D542#),(16#1D543#,16#1D543#,16#1D543#),
         (16#1D544#,16#1D544#,16#1D544#),(16#1D546#,16#1D546#,16#1D546#),(16#1D54A#,16#1D54A#,16#1D54A#),
         (16#1D54B#,16#1D54B#,16#1D54B#),(16#1D54C#,16#1D54C#,16#1D54C#),(16#1D54D#,16#1D54D#,16#1D54D#),
         (16#1D54E#,16#1D54E#,16#1D54E#),(16#1D54F#,16#1D54F#,16#1D54F#),(16#1D550#,16#1D550#,16#1D550#),
         (16#1D552#,16#1D552#,16#1D552#),(16#1D553#,16#1D553#,16#1D553#),(16#1D554#,16#1D554#,16#1D554#),
         (16#1D555#,16#1D555#,16#1D555#),(16#1D556#,16#1D556#,16#1D556#),(16#1D557#,16#1D557#,16#1D557#),
         (16#1D558#,16#1D558#,16#1D558#),(16#1D559#,16#1D559#,16#1D559#),(16#1D55A#,16#1D55A#,16#1D55A#),
         (16#1D55B#,16#1D55B#,16#1D55B#),(16#1D55C#,16#1D55C#,16#1D55C#),(16#1D55D#,16#1D55D#,16#1D55D#),
         (16#1D55E#,16#1D55E#,16#1D55E#),(16#1D55F#,16#1D55F#,16#1D55F#),(16#1D560#,16#1D560#,16#1D560#),
         (16#1D561#,16#1D561#,16#1D561#),(16#1D562#,16#1D562#,16#1D562#),(16#1D563#,16#1D563#,16#1D563#),
         (16#1D564#,16#1D564#,16#1D564#),(16#1D565#,16#1D565#,16#1D565#),(16#1D566#,16#1D566#,16#1D566#),
         (16#1D567#,16#1D567#,16#1D567#),(16#1D568#,16#1D568#,16#1D568#),(16#1D569#,16#1D569#,16#1D569#),
         (16#1D56A#,16#1D56A#,16#1D56A#),(16#1D56B#,16#1D56B#,16#1D56B#),(16#1D56C#,16#1D56C#,16#1D56C#),
         (16#1D56D#,16#1D56D#,16#1D56D#),(16#1D56E#,16#1D56E#,16#1D56E#),(16#1D56F#,16#1D56F#,16#1D56F#),
         (16#1D570#,16#1D570#,16#1D570#),(16#1D571#,16#1D571#,16#1D571#),(16#1D572#,16#1D572#,16#1D572#),
         (16#1D573#,16#1D573#,16#1D573#),(16#1D574#,16#1D574#,16#1D574#),(16#1D575#,16#1D575#,16#1D575#),
         (16#1D576#,16#1D576#,16#1D576#),(16#1D577#,16#1D577#,16#1D577#),(16#1D578#,16#1D578#,16#1D578#),
         (16#1D579#,16#1D579#,16#1D579#),(16#1D57A#,16#1D57A#,16#1D57A#),(16#1D57B#,16#1D57B#,16#1D57B#),
         (16#1D57C#,16#1D57C#,16#1D57C#),(16#1D57D#,16#1D57D#,16#1D57D#),(16#1D57E#,16#1D57E#,16#1D57E#),
         (16#1D57F#,16#1D57F#,16#1D57F#),(16#1D580#,16#1D580#,16#1D580#),(16#1D581#,16#1D581#,16#1D581#),
         (16#1D582#,16#1D582#,16#1D582#),(16#1D583#,16#1D583#,16#1D583#),(16#1D584#,16#1D584#,16#1D584#),
         (16#1D585#,16#1D585#,16#1D585#),(16#1D586#,16#1D586#,16#1D586#),(16#1D587#,16#1D587#,16#1D587#),
         (16#1D588#,16#1D588#,16#1D588#),(16#1D589#,16#1D589#,16#1D589#),(16#1D58A#,16#1D58A#,16#1D58A#),
         (16#1D58B#,16#1D58B#,16#1D58B#),(16#1D58C#,16#1D58C#,16#1D58C#),(16#1D58D#,16#1D58D#,16#1D58D#),
         (16#1D58E#,16#1D58E#,16#1D58E#),(16#1D58F#,16#1D58F#,16#1D58F#),(16#1D590#,16#1D590#,16#1D590#),
         (16#1D591#,16#1D591#,16#1D591#),(16#1D592#,16#1D592#,16#1D592#),(16#1D593#,16#1D593#,16#1D593#),
         (16#1D594#,16#1D594#,16#1D594#),(16#1D595#,16#1D595#,16#1D595#),(16#1D596#,16#1D596#,16#1D596#),
         (16#1D597#,16#1D597#,16#1D597#),(16#1D598#,16#1D598#,16#1D598#),(16#1D599#,16#1D599#,16#1D599#),
         (16#1D59A#,16#1D59A#,16#1D59A#),(16#1D59B#,16#1D59B#,16#1D59B#),(16#1D59C#,16#1D59C#,16#1D59C#),
         (16#1D59D#,16#1D59D#,16#1D59D#),(16#1D59E#,16#1D59E#,16#1D59E#),(16#1D59F#,16#1D59F#,16#1D59F#),
         (16#1D5A0#,16#1D5A0#,16#1D5A0#),(16#1D5A1#,16#1D5A1#,16#1D5A1#),(16#1D5A2#,16#1D5A2#,16#1D5A2#),
         (16#1D5A3#,16#1D5A3#,16#1D5A3#),(16#1D5A4#,16#1D5A4#,16#1D5A4#),(16#1D5A5#,16#1D5A5#,16#1D5A5#),
         (16#1D5A6#,16#1D5A6#,16#1D5A6#),(16#1D5A7#,16#1D5A7#,16#1D5A7#),(16#1D5A8#,16#1D5A8#,16#1D5A8#),
         (16#1D5A9#,16#1D5A9#,16#1D5A9#),(16#1D5AA#,16#1D5AA#,16#1D5AA#),(16#1D5AB#,16#1D5AB#,16#1D5AB#),
         (16#1D5AC#,16#1D5AC#,16#1D5AC#),(16#1D5AD#,16#1D5AD#,16#1D5AD#),(16#1D5AE#,16#1D5AE#,16#1D5AE#),
         (16#1D5AF#,16#1D5AF#,16#1D5AF#),(16#1D5B0#,16#1D5B0#,16#1D5B0#),(16#1D5B1#,16#1D5B1#,16#1D5B1#),
         (16#1D5B2#,16#1D5B2#,16#1D5B2#),(16#1D5B3#,16#1D5B3#,16#1D5B3#),(16#1D5B4#,16#1D5B4#,16#1D5B4#),
         (16#1D5B5#,16#1D5B5#,16#1D5B5#),(16#1D5B6#,16#1D5B6#,16#1D5B6#),(16#1D5B7#,16#1D5B7#,16#1D5B7#),
         (16#1D5B8#,16#1D5B8#,16#1D5B8#),(16#1D5B9#,16#1D5B9#,16#1D5B9#),(16#1D5BA#,16#1D5BA#,16#1D5BA#),
         (16#1D5BB#,16#1D5BB#,16#1D5BB#),(16#1D5BC#,16#1D5BC#,16#1D5BC#),(16#1D5BD#,16#1D5BD#,16#1D5BD#),
         (16#1D5BE#,16#1D5BE#,16#1D5BE#),(16#1D5BF#,16#1D5BF#,16#1D5BF#),(16#1D5C0#,16#1D5C0#,16#1D5C0#),
         (16#1D5C1#,16#1D5C1#,16#1D5C1#),(16#1D5C2#,16#1D5C2#,16#1D5C2#),(16#1D5C3#,16#1D5C3#,16#1D5C3#),
         (16#1D5C4#,16#1D5C4#,16#1D5C4#),(16#1D5C5#,16#1D5C5#,16#1D5C5#),(16#1D5C6#,16#1D5C6#,16#1D5C6#),
         (16#1D5C7#,16#1D5C7#,16#1D5C7#),(16#1D5C8#,16#1D5C8#,16#1D5C8#),(16#1D5C9#,16#1D5C9#,16#1D5C9#),
         (16#1D5CA#,16#1D5CA#,16#1D5CA#),(16#1D5CB#,16#1D5CB#,16#1D5CB#),(16#1D5CC#,16#1D5CC#,16#1D5CC#),
         (16#1D5CD#,16#1D5CD#,16#1D5CD#),(16#1D5CE#,16#1D5CE#,16#1D5CE#),(16#1D5CF#,16#1D5CF#,16#1D5CF#),
         (16#1D5D0#,16#1D5D0#,16#1D5D0#),(16#1D5D1#,16#1D5D1#,16#1D5D1#),(16#1D5D2#,16#1D5D2#,16#1D5D2#),
         (16#1D5D3#,16#1D5D3#,16#1D5D3#),(16#1D5D4#,16#1D5D4#,16#1D5D4#),(16#1D5D5#,16#1D5D5#,16#1D5D5#),
         (16#1D5D6#,16#1D5D6#,16#1D5D6#),(16#1D5D7#,16#1D5D7#,16#1D5D7#),(16#1D5D8#,16#1D5D8#,16#1D5D8#),
         (16#1D5D9#,16#1D5D9#,16#1D5D9#),(16#1D5DA#,16#1D5DA#,16#1D5DA#),(16#1D5DB#,16#1D5DB#,16#1D5DB#),
         (16#1D5DC#,16#1D5DC#,16#1D5DC#),(16#1D5DD#,16#1D5DD#,16#1D5DD#),(16#1D5DE#,16#1D5DE#,16#1D5DE#),
         (16#1D5DF#,16#1D5DF#,16#1D5DF#),(16#1D5E0#,16#1D5E0#,16#1D5E0#),(16#1D5E1#,16#1D5E1#,16#1D5E1#),
         (16#1D5E2#,16#1D5E2#,16#1D5E2#),(16#1D5E3#,16#1D5E3#,16#1D5E3#),(16#1D5E4#,16#1D5E4#,16#1D5E4#),
         (16#1D5E5#,16#1D5E5#,16#1D5E5#),(16#1D5E6#,16#1D5E6#,16#1D5E6#),(16#1D5E7#,16#1D5E7#,16#1D5E7#),
         (16#1D5E8#,16#1D5E8#,16#1D5E8#),(16#1D5E9#,16#1D5E9#,16#1D5E9#),(16#1D5EA#,16#1D5EA#,16#1D5EA#),
         (16#1D5EB#,16#1D5EB#,16#1D5EB#),(16#1D5EC#,16#1D5EC#,16#1D5EC#),(16#1D5ED#,16#1D5ED#,16#1D5ED#),
         (16#1D5EE#,16#1D5EE#,16#1D5EE#),(16#1D5EF#,16#1D5EF#,16#1D5EF#),(16#1D5F0#,16#1D5F0#,16#1D5F0#),
         (16#1D5F1#,16#1D5F1#,16#1D5F1#),(16#1D5F2#,16#1D5F2#,16#1D5F2#),(16#1D5F3#,16#1D5F3#,16#1D5F3#),
         (16#1D5F4#,16#1D5F4#,16#1D5F4#),(16#1D5F5#,16#1D5F5#,16#1D5F5#),(16#1D5F6#,16#1D5F6#,16#1D5F6#),
         (16#1D5F7#,16#1D5F7#,16#1D5F7#),(16#1D5F8#,16#1D5F8#,16#1D5F8#),(16#1D5F9#,16#1D5F9#,16#1D5F9#),
         (16#1D5FA#,16#1D5FA#,16#1D5FA#),(16#1D5FB#,16#1D5FB#,16#1D5FB#),(16#1D5FC#,16#1D5FC#,16#1D5FC#),
         (16#1D5FD#,16#1D5FD#,16#1D5FD#),(16#1D5FE#,16#1D5FE#,16#1D5FE#),(16#1D5FF#,16#1D5FF#,16#1D5FF#),
         (16#1D600#,16#1D600#,16#1D600#),(16#1D601#,16#1D601#,16#1D601#),(16#1D602#,16#1D602#,16#1D602#),
         (16#1D603#,16#1D603#,16#1D603#),(16#1D604#,16#1D604#,16#1D604#),(16#1D605#,16#1D605#,16#1D605#),
         (16#1D606#,16#1D606#,16#1D606#),(16#1D607#,16#1D607#,16#1D607#),(16#1D608#,16#1D608#,16#1D608#),
         (16#1D609#,16#1D609#,16#1D609#),(16#1D60A#,16#1D60A#,16#1D60A#),(16#1D60B#,16#1D60B#,16#1D60B#),
         (16#1D60C#,16#1D60C#,16#1D60C#),(16#1D60D#,16#1D60D#,16#1D60D#),(16#1D60E#,16#1D60E#,16#1D60E#),
         (16#1D60F#,16#1D60F#,16#1D60F#),(16#1D610#,16#1D610#,16#1D610#),(16#1D611#,16#1D611#,16#1D611#),
         (16#1D612#,16#1D612#,16#1D612#),(16#1D613#,16#1D613#,16#1D613#),(16#1D614#,16#1D614#,16#1D614#),
         (16#1D615#,16#1D615#,16#1D615#),(16#1D616#,16#1D616#,16#1D616#),(16#1D617#,16#1D617#,16#1D617#),
         (16#1D618#,16#1D618#,16#1D618#),(16#1D619#,16#1D619#,16#1D619#),(16#1D61A#,16#1D61A#,16#1D61A#),
         (16#1D61B#,16#1D61B#,16#1D61B#),(16#1D61C#,16#1D61C#,16#1D61C#),(16#1D61D#,16#1D61D#,16#1D61D#),
         (16#1D61E#,16#1D61E#,16#1D61E#),(16#1D61F#,16#1D61F#,16#1D61F#),(16#1D620#,16#1D620#,16#1D620#),
         (16#1D621#,16#1D621#,16#1D621#),(16#1D622#,16#1D622#,16#1D622#),(16#1D623#,16#1D623#,16#1D623#),
         (16#1D624#,16#1D624#,16#1D624#),(16#1D625#,16#1D625#,16#1D625#),(16#1D626#,16#1D626#,16#1D626#),
         (16#1D627#,16#1D627#,16#1D627#),(16#1D628#,16#1D628#,16#1D628#),(16#1D629#,16#1D629#,16#1D629#),
         (16#1D62A#,16#1D62A#,16#1D62A#),(16#1D62B#,16#1D62B#,16#1D62B#),(16#1D62C#,16#1D62C#,16#1D62C#),
         (16#1D62D#,16#1D62D#,16#1D62D#),(16#1D62E#,16#1D62E#,16#1D62E#),(16#1D62F#,16#1D62F#,16#1D62F#),
         (16#1D630#,16#1D630#,16#1D630#),(16#1D631#,16#1D631#,16#1D631#),(16#1D632#,16#1D632#,16#1D632#),
         (16#1D633#,16#1D633#,16#1D633#),(16#1D634#,16#1D634#,16#1D634#),(16#1D635#,16#1D635#,16#1D635#),
         (16#1D636#,16#1D636#,16#1D636#),(16#1D637#,16#1D637#,16#1D637#),(16#1D638#,16#1D638#,16#1D638#),
         (16#1D639#,16#1D639#,16#1D639#),(16#1D63A#,16#1D63A#,16#1D63A#),(16#1D63B#,16#1D63B#,16#1D63B#),
         (16#1D63C#,16#1D63C#,16#1D63C#),(16#1D63D#,16#1D63D#,16#1D63D#),(16#1D63E#,16#1D63E#,16#1D63E#),
         (16#1D63F#,16#1D63F#,16#1D63F#),(16#1D640#,16#1D640#,16#1D640#),(16#1D641#,16#1D641#,16#1D641#),
         (16#1D642#,16#1D642#,16#1D642#),(16#1D643#,16#1D643#,16#1D643#),(16#1D644#,16#1D644#,16#1D644#),
         (16#1D645#,16#1D645#,16#1D645#),(16#1D646#,16#1D646#,16#1D646#),(16#1D647#,16#1D647#,16#1D647#),
         (16#1D648#,16#1D648#,16#1D648#),(16#1D649#,16#1D649#,16#1D649#),(16#1D64A#,16#1D64A#,16#1D64A#),
         (16#1D64B#,16#1D64B#,16#1D64B#),(16#1D64C#,16#1D64C#,16#1D64C#),(16#1D64D#,16#1D64D#,16#1D64D#),
         (16#1D64E#,16#1D64E#,16#1D64E#),(16#1D64F#,16#1D64F#,16#1D64F#),(16#1D650#,16#1D650#,16#1D650#),
         (16#1D651#,16#1D651#,16#1D651#),(16#1D652#,16#1D652#,16#1D652#),(16#1D653#,16#1D653#,16#1D653#),
         (16#1D654#,16#1D654#,16#1D654#),(16#1D655#,16#1D655#,16#1D655#),(16#1D656#,16#1D656#,16#1D656#),
         (16#1D657#,16#1D657#,16#1D657#),(16#1D658#,16#1D658#,16#1D658#),(16#1D659#,16#1D659#,16#1D659#),
         (16#1D65A#,16#1D65A#,16#1D65A#),(16#1D65B#,16#1D65B#,16#1D65B#),(16#1D65C#,16#1D65C#,16#1D65C#),
         (16#1D65D#,16#1D65D#,16#1D65D#),(16#1D65E#,16#1D65E#,16#1D65E#),(16#1D65F#,16#1D65F#,16#1D65F#),
         (16#1D660#,16#1D660#,16#1D660#),(16#1D661#,16#1D661#,16#1D661#),(16#1D662#,16#1D662#,16#1D662#),
         (16#1D663#,16#1D663#,16#1D663#),(16#1D664#,16#1D664#,16#1D664#),(16#1D665#,16#1D665#,16#1D665#),
         (16#1D666#,16#1D666#,16#1D666#),(16#1D667#,16#1D667#,16#1D667#),(16#1D668#,16#1D668#,16#1D668#),
         (16#1D669#,16#1D669#,16#1D669#),(16#1D66A#,16#1D66A#,16#1D66A#),(16#1D66B#,16#1D66B#,16#1D66B#),
         (16#1D66C#,16#1D66C#,16#1D66C#),(16#1D66D#,16#1D66D#,16#1D66D#),(16#1D66E#,16#1D66E#,16#1D66E#),
         (16#1D66F#,16#1D66F#,16#1D66F#),(16#1D670#,16#1D670#,16#1D670#),(16#1D671#,16#1D671#,16#1D671#),
         (16#1D672#,16#1D672#,16#1D672#),(16#1D673#,16#1D673#,16#1D673#),(16#1D674#,16#1D674#,16#1D674#),
         (16#1D675#,16#1D675#,16#1D675#),(16#1D676#,16#1D676#,16#1D676#),(16#1D677#,16#1D677#,16#1D677#),
         (16#1D678#,16#1D678#,16#1D678#),(16#1D679#,16#1D679#,16#1D679#),(16#1D67A#,16#1D67A#,16#1D67A#),
         (16#1D67B#,16#1D67B#,16#1D67B#),(16#1D67C#,16#1D67C#,16#1D67C#),(16#1D67D#,16#1D67D#,16#1D67D#),
         (16#1D67E#,16#1D67E#,16#1D67E#),(16#1D67F#,16#1D67F#,16#1D67F#),(16#1D680#,16#1D680#,16#1D680#),
         (16#1D681#,16#1D681#,16#1D681#),(16#1D682#,16#1D682#,16#1D682#),(16#1D683#,16#1D683#,16#1D683#),
         (16#1D684#,16#1D684#,16#1D684#),(16#1D685#,16#1D685#,16#1D685#),(16#1D686#,16#1D686#,16#1D686#),
         (16#1D687#,16#1D687#,16#1D687#),(16#1D688#,16#1D688#,16#1D688#),(16#1D689#,16#1D689#,16#1D689#),
         (16#1D68A#,16#1D68A#,16#1D68A#),(16#1D68B#,16#1D68B#,16#1D68B#),(16#1D68C#,16#1D68C#,16#1D68C#),
         (16#1D68D#,16#1D68D#,16#1D68D#),(16#1D68E#,16#1D68E#,16#1D68E#),(16#1D68F#,16#1D68F#,16#1D68F#),
         (16#1D690#,16#1D690#,16#1D690#),(16#1D691#,16#1D691#,16#1D691#),(16#1D692#,16#1D692#,16#1D692#),
         (16#1D693#,16#1D693#,16#1D693#),(16#1D694#,16#1D694#,16#1D694#),(16#1D695#,16#1D695#,16#1D695#),
         (16#1D696#,16#1D696#,16#1D696#),(16#1D697#,16#1D697#,16#1D697#),(16#1D698#,16#1D698#,16#1D698#),
         (16#1D699#,16#1D699#,16#1D699#),(16#1D69A#,16#1D69A#,16#1D69A#),(16#1D69B#,16#1D69B#,16#1D69B#),
         (16#1D69C#,16#1D69C#,16#1D69C#),(16#1D69D#,16#1D69D#,16#1D69D#),(16#1D69E#,16#1D69E#,16#1D69E#),
         (16#1D69F#,16#1D69F#,16#1D69F#),(16#1D6A0#,16#1D6A0#,16#1D6A0#),(16#1D6A1#,16#1D6A1#,16#1D6A1#),
         (16#1D6A2#,16#1D6A2#,16#1D6A2#),(16#1D6A3#,16#1D6A3#,16#1D6A3#),(16#1D6A4#,16#1D6A4#,16#1D6A4#),
         (16#1D6A5#,16#1D6A5#,16#1D6A5#),(16#1D6A8#,16#1D6A8#,16#1D6A8#),(16#1D6A9#,16#1D6A9#,16#1D6A9#),
         (16#1D6AA#,16#1D6AA#,16#1D6AA#),(16#1D6AB#,16#1D6AB#,16#1D6AB#),(16#1D6AC#,16#1D6AC#,16#1D6AC#),
         (16#1D6AD#,16#1D6AD#,16#1D6AD#),(16#1D6AE#,16#1D6AE#,16#1D6AE#),(16#1D6AF#,16#1D6AF#,16#1D6AF#),
         (16#1D6B0#,16#1D6B0#,16#1D6B0#),(16#1D6B1#,16#1D6B1#,16#1D6B1#),(16#1D6B2#,16#1D6B2#,16#1D6B2#),
         (16#1D6B3#,16#1D6B3#,16#1D6B3#),(16#1D6B4#,16#1D6B4#,16#1D6B4#),(16#1D6B5#,16#1D6B5#,16#1D6B5#),
         (16#1D6B6#,16#1D6B6#,16#1D6B6#),(16#1D6B7#,16#1D6B7#,16#1D6B7#),(16#1D6B8#,16#1D6B8#,16#1D6B8#),
         (16#1D6B9#,16#1D6B9#,16#1D6B9#),(16#1D6BA#,16#1D6BA#,16#1D6BA#),(16#1D6BB#,16#1D6BB#,16#1D6BB#),
         (16#1D6BC#,16#1D6BC#,16#1D6BC#),(16#1D6BD#,16#1D6BD#,16#1D6BD#),(16#1D6BE#,16#1D6BE#,16#1D6BE#),
         (16#1D6BF#,16#1D6BF#,16#1D6BF#),(16#1D6C0#,16#1D6C0#,16#1D6C0#),(16#1D6C2#,16#1D6C2#,16#1D6C2#),
         (16#1D6C3#,16#1D6C3#,16#1D6C3#),(16#1D6C4#,16#1D6C4#,16#1D6C4#),(16#1D6C5#,16#1D6C5#,16#1D6C5#),
         (16#1D6C6#,16#1D6C6#,16#1D6C6#),(16#1D6C7#,16#1D6C7#,16#1D6C7#),(16#1D6C8#,16#1D6C8#,16#1D6C8#),
         (16#1D6C9#,16#1D6C9#,16#1D6C9#),(16#1D6CA#,16#1D6CA#,16#1D6CA#),(16#1D6CB#,16#1D6CB#,16#1D6CB#),
         (16#1D6CC#,16#1D6CC#,16#1D6CC#),(16#1D6CD#,16#1D6CD#,16#1D6CD#),(16#1D6CE#,16#1D6CE#,16#1D6CE#),
         (16#1D6CF#,16#1D6CF#,16#1D6CF#),(16#1D6D0#,16#1D6D0#,16#1D6D0#),(16#1D6D1#,16#1D6D1#,16#1D6D1#),
         (16#1D6D2#,16#1D6D2#,16#1D6D2#),(16#1D6D3#,16#1D6D3#,16#1D6D3#),(16#1D6D4#,16#1D6D4#,16#1D6D4#),
         (16#1D6D5#,16#1D6D5#,16#1D6D5#),(16#1D6D6#,16#1D6D6#,16#1D6D6#),(16#1D6D7#,16#1D6D7#,16#1D6D7#),
         (16#1D6D8#,16#1D6D8#,16#1D6D8#),(16#1D6D9#,16#1D6D9#,16#1D6D9#),(16#1D6DA#,16#1D6DA#,16#1D6DA#),
         (16#1D6DC#,16#1D6DC#,16#1D6DC#),(16#1D6DD#,16#1D6DD#,16#1D6DD#),(16#1D6DE#,16#1D6DE#,16#1D6DE#),
         (16#1D6DF#,16#1D6DF#,16#1D6DF#),(16#1D6E0#,16#1D6E0#,16#1D6E0#),(16#1D6E1#,16#1D6E1#,16#1D6E1#),
         (16#1D6E2#,16#1D6E2#,16#1D6E2#),(16#1D6E3#,16#1D6E3#,16#1D6E3#),(16#1D6E4#,16#1D6E4#,16#1D6E4#),
         (16#1D6E5#,16#1D6E5#,16#1D6E5#),(16#1D6E6#,16#1D6E6#,16#1D6E6#),(16#1D6E7#,16#1D6E7#,16#1D6E7#),
         (16#1D6E8#,16#1D6E8#,16#1D6E8#),(16#1D6E9#,16#1D6E9#,16#1D6E9#),(16#1D6EA#,16#1D6EA#,16#1D6EA#),
         (16#1D6EB#,16#1D6EB#,16#1D6EB#),(16#1D6EC#,16#1D6EC#,16#1D6EC#),(16#1D6ED#,16#1D6ED#,16#1D6ED#),
         (16#1D6EE#,16#1D6EE#,16#1D6EE#),(16#1D6EF#,16#1D6EF#,16#1D6EF#),(16#1D6F0#,16#1D6F0#,16#1D6F0#),
         (16#1D6F1#,16#1D6F1#,16#1D6F1#),(16#1D6F2#,16#1D6F2#,16#1D6F2#),(16#1D6F3#,16#1D6F3#,16#1D6F3#),
         (16#1D6F4#,16#1D6F4#,16#1D6F4#),(16#1D6F5#,16#1D6F5#,16#1D6F5#),(16#1D6F6#,16#1D6F6#,16#1D6F6#),
         (16#1D6F7#,16#1D6F7#,16#1D6F7#),(16#1D6F8#,16#1D6F8#,16#1D6F8#),(16#1D6F9#,16#1D6F9#,16#1D6F9#),
         (16#1D6FA#,16#1D6FA#,16#1D6FA#),(16#1D6FC#,16#1D6FC#,16#1D6FC#),(16#1D6FD#,16#1D6FD#,16#1D6FD#),
         (16#1D6FE#,16#1D6FE#,16#1D6FE#),(16#1D6FF#,16#1D6FF#,16#1D6FF#),(16#1D700#,16#1D700#,16#1D700#),
         (16#1D701#,16#1D701#,16#1D701#),(16#1D702#,16#1D702#,16#1D702#),(16#1D703#,16#1D703#,16#1D703#),
         (16#1D704#,16#1D704#,16#1D704#),(16#1D705#,16#1D705#,16#1D705#),(16#1D706#,16#1D706#,16#1D706#),
         (16#1D707#,16#1D707#,16#1D707#),(16#1D708#,16#1D708#,16#1D708#),(16#1D709#,16#1D709#,16#1D709#),
         (16#1D70A#,16#1D70A#,16#1D70A#),(16#1D70B#,16#1D70B#,16#1D70B#),(16#1D70C#,16#1D70C#,16#1D70C#),
         (16#1D70D#,16#1D70D#,16#1D70D#),(16#1D70E#,16#1D70E#,16#1D70E#),(16#1D70F#,16#1D70F#,16#1D70F#),
         (16#1D710#,16#1D710#,16#1D710#),(16#1D711#,16#1D711#,16#1D711#),(16#1D712#,16#1D712#,16#1D712#),
         (16#1D713#,16#1D713#,16#1D713#),(16#1D714#,16#1D714#,16#1D714#),(16#1D716#,16#1D716#,16#1D716#),
         (16#1D717#,16#1D717#,16#1D717#),(16#1D718#,16#1D718#,16#1D718#),(16#1D719#,16#1D719#,16#1D719#),
         (16#1D71A#,16#1D71A#,16#1D71A#),(16#1D71B#,16#1D71B#,16#1D71B#),(16#1D71C#,16#1D71C#,16#1D71C#),
         (16#1D71D#,16#1D71D#,16#1D71D#),(16#1D71E#,16#1D71E#,16#1D71E#),(16#1D71F#,16#1D71F#,16#1D71F#),
         (16#1D720#,16#1D720#,16#1D720#),(16#1D721#,16#1D721#,16#1D721#),(16#1D722#,16#1D722#,16#1D722#),
         (16#1D723#,16#1D723#,16#1D723#),(16#1D724#,16#1D724#,16#1D724#),(16#1D725#,16#1D725#,16#1D725#),
         (16#1D726#,16#1D726#,16#1D726#),(16#1D727#,16#1D727#,16#1D727#),(16#1D728#,16#1D728#,16#1D728#),
         (16#1D729#,16#1D729#,16#1D729#),(16#1D72A#,16#1D72A#,16#1D72A#),(16#1D72B#,16#1D72B#,16#1D72B#),
         (16#1D72C#,16#1D72C#,16#1D72C#),(16#1D72D#,16#1D72D#,16#1D72D#),(16#1D72E#,16#1D72E#,16#1D72E#),
         (16#1D72F#,16#1D72F#,16#1D72F#),(16#1D730#,16#1D730#,16#1D730#),(16#1D731#,16#1D731#,16#1D731#),
         (16#1D732#,16#1D732#,16#1D732#),(16#1D733#,16#1D733#,16#1D733#),(16#1D734#,16#1D734#,16#1D734#),
         (16#1D736#,16#1D736#,16#1D736#),(16#1D737#,16#1D737#,16#1D737#),(16#1D738#,16#1D738#,16#1D738#),
         (16#1D739#,16#1D739#,16#1D739#),(16#1D73A#,16#1D73A#,16#1D73A#),(16#1D73B#,16#1D73B#,16#1D73B#),
         (16#1D73C#,16#1D73C#,16#1D73C#),(16#1D73D#,16#1D73D#,16#1D73D#),(16#1D73E#,16#1D73E#,16#1D73E#),
         (16#1D73F#,16#1D73F#,16#1D73F#),(16#1D740#,16#1D740#,16#1D740#),(16#1D741#,16#1D741#,16#1D741#),
         (16#1D742#,16#1D742#,16#1D742#),(16#1D743#,16#1D743#,16#1D743#),(16#1D744#,16#1D744#,16#1D744#),
         (16#1D745#,16#1D745#,16#1D745#),(16#1D746#,16#1D746#,16#1D746#),(16#1D747#,16#1D747#,16#1D747#),
         (16#1D748#,16#1D748#,16#1D748#),(16#1D749#,16#1D749#,16#1D749#),(16#1D74A#,16#1D74A#,16#1D74A#),
         (16#1D74B#,16#1D74B#,16#1D74B#),(16#1D74C#,16#1D74C#,16#1D74C#),(16#1D74D#,16#1D74D#,16#1D74D#),
         (16#1D74E#,16#1D74E#,16#1D74E#),(16#1D750#,16#1D750#,16#1D750#),(16#1D751#,16#1D751#,16#1D751#),
         (16#1D752#,16#1D752#,16#1D752#),(16#1D753#,16#1D753#,16#1D753#),(16#1D754#,16#1D754#,16#1D754#),
         (16#1D755#,16#1D755#,16#1D755#),(16#1D756#,16#1D756#,16#1D756#),(16#1D757#,16#1D757#,16#1D757#),
         (16#1D758#,16#1D758#,16#1D758#),(16#1D759#,16#1D759#,16#1D759#),(16#1D75A#,16#1D75A#,16#1D75A#),
         (16#1D75B#,16#1D75B#,16#1D75B#),(16#1D75C#,16#1D75C#,16#1D75C#),(16#1D75D#,16#1D75D#,16#1D75D#),
         (16#1D75E#,16#1D75E#,16#1D75E#),(16#1D75F#,16#1D75F#,16#1D75F#),(16#1D760#,16#1D760#,16#1D760#),
         (16#1D761#,16#1D761#,16#1D761#),(16#1D762#,16#1D762#,16#1D762#),(16#1D763#,16#1D763#,16#1D763#),
         (16#1D764#,16#1D764#,16#1D764#),(16#1D765#,16#1D765#,16#1D765#),(16#1D766#,16#1D766#,16#1D766#),
         (16#1D767#,16#1D767#,16#1D767#),(16#1D768#,16#1D768#,16#1D768#),(16#1D769#,16#1D769#,16#1D769#),
         (16#1D76A#,16#1D76A#,16#1D76A#),(16#1D76B#,16#1D76B#,16#1D76B#),(16#1D76C#,16#1D76C#,16#1D76C#),
         (16#1D76D#,16#1D76D#,16#1D76D#),(16#1D76E#,16#1D76E#,16#1D76E#),(16#1D770#,16#1D770#,16#1D770#),
         (16#1D771#,16#1D771#,16#1D771#),(16#1D772#,16#1D772#,16#1D772#),(16#1D773#,16#1D773#,16#1D773#),
         (16#1D774#,16#1D774#,16#1D774#),(16#1D775#,16#1D775#,16#1D775#),(16#1D776#,16#1D776#,16#1D776#),
         (16#1D777#,16#1D777#,16#1D777#),(16#1D778#,16#1D778#,16#1D778#),(16#1D779#,16#1D779#,16#1D779#),
         (16#1D77A#,16#1D77A#,16#1D77A#),(16#1D77B#,16#1D77B#,16#1D77B#),(16#1D77C#,16#1D77C#,16#1D77C#),
         (16#1D77D#,16#1D77D#,16#1D77D#),(16#1D77E#,16#1D77E#,16#1D77E#),(16#1D77F#,16#1D77F#,16#1D77F#),
         (16#1D780#,16#1D780#,16#1D780#),(16#1D781#,16#1D781#,16#1D781#),(16#1D782#,16#1D782#,16#1D782#),
         (16#1D783#,16#1D783#,16#1D783#),(16#1D784#,16#1D784#,16#1D784#),(16#1D785#,16#1D785#,16#1D785#),
         (16#1D786#,16#1D786#,16#1D786#),(16#1D787#,16#1D787#,16#1D787#),(16#1D788#,16#1D788#,16#1D788#),
         (16#1D78A#,16#1D78A#,16#1D78A#),(16#1D78B#,16#1D78B#,16#1D78B#),(16#1D78C#,16#1D78C#,16#1D78C#),
         (16#1D78D#,16#1D78D#,16#1D78D#),(16#1D78E#,16#1D78E#,16#1D78E#),(16#1D78F#,16#1D78F#,16#1D78F#),
         (16#1D790#,16#1D790#,16#1D790#),(16#1D791#,16#1D791#,16#1D791#),(16#1D792#,16#1D792#,16#1D792#),
         (16#1D793#,16#1D793#,16#1D793#),(16#1D794#,16#1D794#,16#1D794#),(16#1D795#,16#1D795#,16#1D795#),
         (16#1D796#,16#1D796#,16#1D796#),(16#1D797#,16#1D797#,16#1D797#),(16#1D798#,16#1D798#,16#1D798#),
         (16#1D799#,16#1D799#,16#1D799#),(16#1D79A#,16#1D79A#,16#1D79A#),(16#1D79B#,16#1D79B#,16#1D79B#),
         (16#1D79C#,16#1D79C#,16#1D79C#),(16#1D79D#,16#1D79D#,16#1D79D#),(16#1D79E#,16#1D79E#,16#1D79E#),
         (16#1D79F#,16#1D79F#,16#1D79F#),(16#1D7A0#,16#1D7A0#,16#1D7A0#),(16#1D7A1#,16#1D7A1#,16#1D7A1#),
         (16#1D7A2#,16#1D7A2#,16#1D7A2#),(16#1D7A3#,16#1D7A3#,16#1D7A3#),(16#1D7A4#,16#1D7A4#,16#1D7A4#),
         (16#1D7A5#,16#1D7A5#,16#1D7A5#),(16#1D7A6#,16#1D7A6#,16#1D7A6#),(16#1D7A7#,16#1D7A7#,16#1D7A7#),
         (16#1D7A8#,16#1D7A8#,16#1D7A8#),(16#1D7AA#,16#1D7AA#,16#1D7AA#),(16#1D7AB#,16#1D7AB#,16#1D7AB#),
         (16#1D7AC#,16#1D7AC#,16#1D7AC#),(16#1D7AD#,16#1D7AD#,16#1D7AD#),(16#1D7AE#,16#1D7AE#,16#1D7AE#),
         (16#1D7AF#,16#1D7AF#,16#1D7AF#),(16#1D7B0#,16#1D7B0#,16#1D7B0#),(16#1D7B1#,16#1D7B1#,16#1D7B1#),
         (16#1D7B2#,16#1D7B2#,16#1D7B2#),(16#1D7B3#,16#1D7B3#,16#1D7B3#),(16#1D7B4#,16#1D7B4#,16#1D7B4#),
         (16#1D7B5#,16#1D7B5#,16#1D7B5#),(16#1D7B6#,16#1D7B6#,16#1D7B6#),(16#1D7B7#,16#1D7B7#,16#1D7B7#),
         (16#1D7B8#,16#1D7B8#,16#1D7B8#),(16#1D7B9#,16#1D7B9#,16#1D7B9#),(16#1D7BA#,16#1D7BA#,16#1D7BA#),
         (16#1D7BB#,16#1D7BB#,16#1D7BB#),(16#1D7BC#,16#1D7BC#,16#1D7BC#),(16#1D7BD#,16#1D7BD#,16#1D7BD#),
         (16#1D7BE#,16#1D7BE#,16#1D7BE#),(16#1D7BF#,16#1D7BF#,16#1D7BF#),(16#1D7C0#,16#1D7C0#,16#1D7C0#),
         (16#1D7C1#,16#1D7C1#,16#1D7C1#),(16#1D7C2#,16#1D7C2#,16#1D7C2#),(16#1D7C4#,16#1D7C4#,16#1D7C4#),
         (16#1D7C5#,16#1D7C5#,16#1D7C5#),(16#1D7C6#,16#1D7C6#,16#1D7C6#),(16#1D7C7#,16#1D7C7#,16#1D7C7#),
         (16#1D7C8#,16#1D7C8#,16#1D7C8#),(16#1D7C9#,16#1D7C9#,16#1D7C9#),(16#1D7CA#,16#1D7CA#,16#1D7CA#),
         (16#1D7CB#,16#1D7CB#,16#1D7CB#)
        );

      function Image (Value : T) return String_T is
         Result  : String_T (1..4) := (others => ' ');
         Pointer : Int32_T := Int32_T (Result'First);
      begin
         Aida.UTF8.Put (Result, Pointer, Value);
         return Result (1..Positive (Pointer - 1));
      end Image;

      -- The Find procedure can be formally verified by SPARK GPL 2016, Level=None
      -- and it takes around 20 seconds:
      --
      --     procedure Find (Code  : T;
      --                     CA    : Categorization_Array;
      --                     Found : out Boolean;
      --                     Index : in out Categorization_Index) with
      --       Global => null,
      --       Pre => (for all I in CA'Range => (for all J in I..CA'Last => CA (I).Code <= CA (J).Code));
      --
      --     procedure Find (Code  : T;
      --                     CA    : Categorization_Array;
      --                     Found : out Boolean;
      --                     Index : in out Categorization_Index)
      --     is
      --        From : Categorization_Index'Base := Mapping'First;
      --        To   : Categorization_Index'Base := Mapping'Last;
      --        This : Categorization_Index;
      --        Current : Code_Point;
      --     begin
      --        while From <= To loop
      --           pragma Loop_Invariant (From >= CA'First);
      --           pragma Loop_Invariant (To <= CA'Last);
      --           pragma Loop_Invariant (for all I in CA'First..(From - 1) => CA (I).Code < Code);
      --           pragma Loop_Invariant (for all I in (To + 1)..CA'Last => Code < CA (I).Code);
      --
      --           This := From + (To - From) / 2;
      --           Current := CA (This).Code;
      --
      --           if Current < Code then
      --              From := This + 1;
      --           elsif Current > Code then
      --              To := This - 1;
      --           elsif Current = Code then
      --              Found := True;
      --              Index := This;
      --              return;
      --           else
      --              Found := False;
      --              return;
      --           end if;
      --        end loop;
      --        Found := False;
      --     end Find;

      procedure Find (Code  : T;
                      Found : out Boolean;
                      Index : in out Categorization_Index);

      -- Has not been able to formally verify this procedure with SPARK GPL 2016.
      -- But the out-commented Find procedure above can be formally verified.
      procedure Find (Code  : T;
                      Found : out Boolean;
                      Index : in out Categorization_Index)
      is
         From : Categorization_Index'Base := Mapping'First;
         To   : Categorization_Index'Base := Mapping'Last;
         This : Categorization_Index;
         Current : Code_Point_T;
      begin
         while From <= To loop
            This := From + (To - From) / 2;
            Current := Mapping (This).Code;

            if Current < Code then
               From := This + 1;
            elsif Current > Code then
               To := This - 1;
            elsif Current = Code then
               Found := True;
               Index := This;
               return;
            else
               Found := False;
               return;
            end if;
         end loop;
         Found := False;
      end Find;

      -- Verified by: SPARK GPL 2016
      -- Level: None
      -- Elapsed time: 12 seconds
      function Is_Uppercase (Value : T) return Boolean is
         Index : Categorization_Index := Categorization_Index'First;
         Found : Boolean;
      begin
         Find (Value, Found, Index);
         if Found then
            return Mapping (Index).Upper = Value;
         else
            return False;
         end if;
      end Is_Uppercase;

      -- Verified by: SPARK GPL 2016
      -- Level: None
      -- Elapsed time: 12 seconds
      function Has_Case (Value : T) return Boolean is
         Index : Categorization_Index := Categorization_Index'First;
         Found : Boolean;
      begin
         Find (Value, Found, Index);
         if Found then
            return (Mapping (Index).Lower = Value or else Mapping (Index).Upper = Value);
         else
            return False;
         end if;
      end Has_Case;

      -- Verified by: SPARK GPL 2016
      -- Level: None
      -- Elapsed time: 12 seconds
      function Is_Lowercase (Value : T) return Boolean is
         Index : Categorization_Index := Categorization_Index'First;
         Found : Boolean;
      begin
         Find (Value, Found, Index);
         if Found then
            return Mapping (Index).Lower = Value;
         else
            return False;
         end if;
      end Is_Lowercase;

      -- Verified by: SPARK GPL 2016
      -- Level: None
      -- Elapsed time: 12 seconds
      function To_Lowercase (Value : T) return T is
         Index : Categorization_Index := Categorization_Index'First;
         Found : Boolean;
      begin
         Find (Value, Found, Index);
         if Found then
            return Mapping (Index).Lower;
         else
            return Value;
         end if;
      end To_Lowercase;

      -- Verified by: SPARK GPL 2016
      -- Level: None
      -- Elapsed time: 12 seconds
      function To_Uppercase (Value : T) return T is
         Index : Categorization_Index := Categorization_Index'First;
         Found : Boolean;
      begin
         Find (Value, Found, Index);
         if Found then
            return Mapping (Index).Upper;
         else
            return Value;
         end if;
      end To_Uppercase;

      type Points_Range is record
         From     : T;
         To       : T;
         Category : Fs.General_Category;
      end record;
      type Range_Index is range 1..2077;
      type Range_Array is array (Range_Index) of Points_Range;

      Category_Mapping : constant Range_Array :=
        (
           (16#0#,16#1F#,Fs.CC),(16#20#,16#20#,Fs.ZS),(16#21#,16#23#,Fs.PO),
         (16#24#,16#24#,Fs.SC),(16#25#,16#27#,Fs.PO),(16#28#,16#28#,Fs.PS),
         (16#29#,16#29#,Fs.PE),(16#2A#,16#2A#,Fs.PO),(16#2B#,16#2B#,Fs.SM),
         (16#2C#,16#2C#,Fs.PO),(16#2D#,16#2D#,Fs.PD),(16#2E#,16#2F#,Fs.PO),
         (16#30#,16#39#,Fs.ND),(16#3A#,16#3B#,Fs.PO),(16#3C#,16#3E#,Fs.SM),
         (16#3F#,16#40#,Fs.PO),(16#41#,16#5A#,Fs.LU),(16#5B#,16#5B#,Fs.PS),
         (16#5C#,16#5C#,Fs.PO),(16#5D#,16#5D#,Fs.PE),(16#5E#,16#5E#,Fs.SK),
         (16#5F#,16#5F#,Fs.PC),(16#60#,16#60#,Fs.SK),(16#61#,16#7A#,Fs.LL),
         (16#7B#,16#7B#,Fs.PS),(16#7C#,16#7C#,Fs.SM),(16#7D#,16#7D#,Fs.PE),
         (16#7E#,16#7E#,Fs.SM),(16#7F#,16#9F#,Fs.CC),(16#A0#,16#A0#,Fs.ZS),
         (16#A1#,16#A1#,Fs.PO),(16#A2#,16#A5#,Fs.SC),(16#A6#,16#A7#,Fs.SO),
         (16#A8#,16#A8#,Fs.SK),(16#A9#,16#A9#,Fs.SO),(16#AA#,16#AA#,Fs.LL),
         (16#AB#,16#AB#,Fs.PI),(16#AC#,16#AC#,Fs.SM),(16#AD#,16#AD#,Fs.CF),
         (16#AE#,16#AE#,Fs.SO),(16#AF#,16#AF#,Fs.SK),(16#B0#,16#B0#,Fs.SO),
         (16#B1#,16#B1#,Fs.SM),(16#B2#,16#B3#,Fs.NO),(16#B4#,16#B4#,Fs.SK),
         (16#B5#,16#B5#,Fs.LL),(16#B6#,16#B6#,Fs.SO),(16#B7#,16#B7#,Fs.PO),
         (16#B8#,16#B8#,Fs.SK),(16#B9#,16#B9#,Fs.NO),(16#BA#,16#BA#,Fs.LL),
         (16#BB#,16#BB#,Fs.PF),(16#BC#,16#BE#,Fs.NO),(16#BF#,16#BF#,Fs.PO),
         (16#C0#,16#D6#,Fs.LU),(16#D7#,16#D7#,Fs.SM),(16#D8#,16#DE#,Fs.LU),
         (16#DF#,16#F6#,Fs.LL),(16#F7#,16#F7#,Fs.SM),(16#F8#,16#FF#,Fs.LL),
         (16#100#,16#100#,Fs.LU),(16#101#,16#101#,Fs.LL),(16#102#,16#102#,Fs.LU),
         (16#103#,16#103#,Fs.LL),(16#104#,16#104#,Fs.LU),(16#105#,16#105#,Fs.LL),
         (16#106#,16#106#,Fs.LU),(16#107#,16#107#,Fs.LL),(16#108#,16#108#,Fs.LU),
         (16#109#,16#109#,Fs.LL),(16#10A#,16#10A#,Fs.LU),(16#10B#,16#10B#,Fs.LL),
         (16#10C#,16#10C#,Fs.LU),(16#10D#,16#10D#,Fs.LL),(16#10E#,16#10E#,Fs.LU),
         (16#10F#,16#10F#,Fs.LL),(16#110#,16#110#,Fs.LU),(16#111#,16#111#,Fs.LL),
         (16#112#,16#112#,Fs.LU),(16#113#,16#113#,Fs.LL),(16#114#,16#114#,Fs.LU),
         (16#115#,16#115#,Fs.LL),(16#116#,16#116#,Fs.LU),(16#117#,16#117#,Fs.LL),
         (16#118#,16#118#,Fs.LU),(16#119#,16#119#,Fs.LL),(16#11A#,16#11A#,Fs.LU),
         (16#11B#,16#11B#,Fs.LL),(16#11C#,16#11C#,Fs.LU),(16#11D#,16#11D#,Fs.LL),
         (16#11E#,16#11E#,Fs.LU),(16#11F#,16#11F#,Fs.LL),(16#120#,16#120#,Fs.LU),
         (16#121#,16#121#,Fs.LL),(16#122#,16#122#,Fs.LU),(16#123#,16#123#,Fs.LL),
         (16#124#,16#124#,Fs.LU),(16#125#,16#125#,Fs.LL),(16#126#,16#126#,Fs.LU),
         (16#127#,16#127#,Fs.LL),(16#128#,16#128#,Fs.LU),(16#129#,16#129#,Fs.LL),
         (16#12A#,16#12A#,Fs.LU),(16#12B#,16#12B#,Fs.LL),(16#12C#,16#12C#,Fs.LU),
         (16#12D#,16#12D#,Fs.LL),(16#12E#,16#12E#,Fs.LU),(16#12F#,16#12F#,Fs.LL),
         (16#130#,16#130#,Fs.LU),(16#131#,16#131#,Fs.LL),(16#132#,16#132#,Fs.LU),
         (16#133#,16#133#,Fs.LL),(16#134#,16#134#,Fs.LU),(16#135#,16#135#,Fs.LL),
         (16#136#,16#136#,Fs.LU),(16#137#,16#138#,Fs.LL),(16#139#,16#139#,Fs.LU),
         (16#13A#,16#13A#,Fs.LL),(16#13B#,16#13B#,Fs.LU),(16#13C#,16#13C#,Fs.LL),
         (16#13D#,16#13D#,Fs.LU),(16#13E#,16#13E#,Fs.LL),(16#13F#,16#13F#,Fs.LU),
         (16#140#,16#140#,Fs.LL),(16#141#,16#141#,Fs.LU),(16#142#,16#142#,Fs.LL),
         (16#143#,16#143#,Fs.LU),(16#144#,16#144#,Fs.LL),(16#145#,16#145#,Fs.LU),
         (16#146#,16#146#,Fs.LL),(16#147#,16#147#,Fs.LU),(16#148#,16#149#,Fs.LL),
         (16#14A#,16#14A#,Fs.LU),(16#14B#,16#14B#,Fs.LL),(16#14C#,16#14C#,Fs.LU),
         (16#14D#,16#14D#,Fs.LL),(16#14E#,16#14E#,Fs.LU),(16#14F#,16#14F#,Fs.LL),
         (16#150#,16#150#,Fs.LU),(16#151#,16#151#,Fs.LL),(16#152#,16#152#,Fs.LU),
         (16#153#,16#153#,Fs.LL),(16#154#,16#154#,Fs.LU),(16#155#,16#155#,Fs.LL),
         (16#156#,16#156#,Fs.LU),(16#157#,16#157#,Fs.LL),(16#158#,16#158#,Fs.LU),
         (16#159#,16#159#,Fs.LL),(16#15A#,16#15A#,Fs.LU),(16#15B#,16#15B#,Fs.LL),
         (16#15C#,16#15C#,Fs.LU),(16#15D#,16#15D#,Fs.LL),(16#15E#,16#15E#,Fs.LU),
         (16#15F#,16#15F#,Fs.LL),(16#160#,16#160#,Fs.LU),(16#161#,16#161#,Fs.LL),
         (16#162#,16#162#,Fs.LU),(16#163#,16#163#,Fs.LL),(16#164#,16#164#,Fs.LU),
         (16#165#,16#165#,Fs.LL),(16#166#,16#166#,Fs.LU),(16#167#,16#167#,Fs.LL),
         (16#168#,16#168#,Fs.LU),(16#169#,16#169#,Fs.LL),(16#16A#,16#16A#,Fs.LU),
         (16#16B#,16#16B#,Fs.LL),(16#16C#,16#16C#,Fs.LU),(16#16D#,16#16D#,Fs.LL),
         (16#16E#,16#16E#,Fs.LU),(16#16F#,16#16F#,Fs.LL),(16#170#,16#170#,Fs.LU),
         (16#171#,16#171#,Fs.LL),(16#172#,16#172#,Fs.LU),(16#173#,16#173#,Fs.LL),
         (16#174#,16#174#,Fs.LU),(16#175#,16#175#,Fs.LL),(16#176#,16#176#,Fs.LU),
         (16#177#,16#177#,Fs.LL),(16#178#,16#179#,Fs.LU),(16#17A#,16#17A#,Fs.LL),
         (16#17B#,16#17B#,Fs.LU),(16#17C#,16#17C#,Fs.LL),(16#17D#,16#17D#,Fs.LU),
         (16#17E#,16#180#,Fs.LL),(16#181#,16#182#,Fs.LU),(16#183#,16#183#,Fs.LL),
         (16#184#,16#184#,Fs.LU),(16#185#,16#185#,Fs.LL),(16#186#,16#187#,Fs.LU),
         (16#188#,16#188#,Fs.LL),(16#189#,16#18B#,Fs.LU),(16#18C#,16#18D#,Fs.LL),
         (16#18E#,16#191#,Fs.LU),(16#192#,16#192#,Fs.LL),(16#193#,16#194#,Fs.LU),
         (16#195#,16#195#,Fs.LL),(16#196#,16#198#,Fs.LU),(16#199#,16#19B#,Fs.LL),
         (16#19C#,16#19D#,Fs.LU),(16#19E#,16#19E#,Fs.LL),(16#19F#,16#1A0#,Fs.LU),
         (16#1A1#,16#1A1#,Fs.LL),(16#1A2#,16#1A2#,Fs.LU),(16#1A3#,16#1A3#,Fs.LL),
         (16#1A4#,16#1A4#,Fs.LU),(16#1A5#,16#1A5#,Fs.LL),(16#1A6#,16#1A7#,Fs.LU),
         (16#1A8#,16#1A8#,Fs.LL),(16#1A9#,16#1A9#,Fs.LU),(16#1AA#,16#1AB#,Fs.LL),
         (16#1AC#,16#1AC#,Fs.LU),(16#1AD#,16#1AD#,Fs.LL),(16#1AE#,16#1AF#,Fs.LU),
         (16#1B0#,16#1B0#,Fs.LL),(16#1B1#,16#1B3#,Fs.LU),(16#1B4#,16#1B4#,Fs.LL),
         (16#1B5#,16#1B5#,Fs.LU),(16#1B6#,16#1B6#,Fs.LL),(16#1B7#,16#1B8#,Fs.LU),
         (16#1B9#,16#1BA#,Fs.LL),(16#1BB#,16#1BB#,Fs.LO),(16#1BC#,16#1BC#,Fs.LU),
         (16#1BD#,16#1BF#,Fs.LL),(16#1C0#,16#1C3#,Fs.LO),(16#1C4#,16#1C4#,Fs.LU),
         (16#1C5#,16#1C5#,Fs.LT),(16#1C6#,16#1C6#,Fs.LL),(16#1C7#,16#1C7#,Fs.LU),
         (16#1C8#,16#1C8#,Fs.LT),(16#1C9#,16#1C9#,Fs.LL),(16#1CA#,16#1CA#,Fs.LU),
         (16#1CB#,16#1CB#,Fs.LT),(16#1CC#,16#1CC#,Fs.LL),(16#1CD#,16#1CD#,Fs.LU),
         (16#1CE#,16#1CE#,Fs.LL),(16#1CF#,16#1CF#,Fs.LU),(16#1D0#,16#1D0#,Fs.LL),
         (16#1D1#,16#1D1#,Fs.LU),(16#1D2#,16#1D2#,Fs.LL),(16#1D3#,16#1D3#,Fs.LU),
         (16#1D4#,16#1D4#,Fs.LL),(16#1D5#,16#1D5#,Fs.LU),(16#1D6#,16#1D6#,Fs.LL),
         (16#1D7#,16#1D7#,Fs.LU),(16#1D8#,16#1D8#,Fs.LL),(16#1D9#,16#1D9#,Fs.LU),
         (16#1DA#,16#1DA#,Fs.LL),(16#1DB#,16#1DB#,Fs.LU),(16#1DC#,16#1DD#,Fs.LL),
         (16#1DE#,16#1DE#,Fs.LU),(16#1DF#,16#1DF#,Fs.LL),(16#1E0#,16#1E0#,Fs.LU),
         (16#1E1#,16#1E1#,Fs.LL),(16#1E2#,16#1E2#,Fs.LU),(16#1E3#,16#1E3#,Fs.LL),
         (16#1E4#,16#1E4#,Fs.LU),(16#1E5#,16#1E5#,Fs.LL),(16#1E6#,16#1E6#,Fs.LU),
         (16#1E7#,16#1E7#,Fs.LL),(16#1E8#,16#1E8#,Fs.LU),(16#1E9#,16#1E9#,Fs.LL),
         (16#1EA#,16#1EA#,Fs.LU),(16#1EB#,16#1EB#,Fs.LL),(16#1EC#,16#1EC#,Fs.LU),
         (16#1ED#,16#1ED#,Fs.LL),(16#1EE#,16#1EE#,Fs.LU),(16#1EF#,16#1F0#,Fs.LL),
         (16#1F1#,16#1F1#,Fs.LU),(16#1F2#,16#1F2#,Fs.LT),(16#1F3#,16#1F3#,Fs.LL),
         (16#1F4#,16#1F4#,Fs.LU),(16#1F5#,16#1F5#,Fs.LL),(16#1F6#,16#1F8#,Fs.LU),
         (16#1F9#,16#1F9#,Fs.LL),(16#1FA#,16#1FA#,Fs.LU),(16#1FB#,16#1FB#,Fs.LL),
         (16#1FC#,16#1FC#,Fs.LU),(16#1FD#,16#1FD#,Fs.LL),(16#1FE#,16#1FE#,Fs.LU),
         (16#1FF#,16#1FF#,Fs.LL),(16#200#,16#200#,Fs.LU),(16#201#,16#201#,Fs.LL),
         (16#202#,16#202#,Fs.LU),(16#203#,16#203#,Fs.LL),(16#204#,16#204#,Fs.LU),
         (16#205#,16#205#,Fs.LL),(16#206#,16#206#,Fs.LU),(16#207#,16#207#,Fs.LL),
         (16#208#,16#208#,Fs.LU),(16#209#,16#209#,Fs.LL),(16#20A#,16#20A#,Fs.LU),
         (16#20B#,16#20B#,Fs.LL),(16#20C#,16#20C#,Fs.LU),(16#20D#,16#20D#,Fs.LL),
         (16#20E#,16#20E#,Fs.LU),(16#20F#,16#20F#,Fs.LL),(16#210#,16#210#,Fs.LU),
         (16#211#,16#211#,Fs.LL),(16#212#,16#212#,Fs.LU),(16#213#,16#213#,Fs.LL),
         (16#214#,16#214#,Fs.LU),(16#215#,16#215#,Fs.LL),(16#216#,16#216#,Fs.LU),
         (16#217#,16#217#,Fs.LL),(16#218#,16#218#,Fs.LU),(16#219#,16#219#,Fs.LL),
         (16#21A#,16#21A#,Fs.LU),(16#21B#,16#21B#,Fs.LL),(16#21C#,16#21C#,Fs.LU),
         (16#21D#,16#21D#,Fs.LL),(16#21E#,16#21E#,Fs.LU),(16#21F#,16#21F#,Fs.LL),
         (16#220#,16#220#,Fs.LU),(16#221#,16#221#,Fs.LL),(16#222#,16#222#,Fs.LU),
         (16#223#,16#223#,Fs.LL),(16#224#,16#224#,Fs.LU),(16#225#,16#225#,Fs.LL),
         (16#226#,16#226#,Fs.LU),(16#227#,16#227#,Fs.LL),(16#228#,16#228#,Fs.LU),
         (16#229#,16#229#,Fs.LL),(16#22A#,16#22A#,Fs.LU),(16#22B#,16#22B#,Fs.LL),
         (16#22C#,16#22C#,Fs.LU),(16#22D#,16#22D#,Fs.LL),(16#22E#,16#22E#,Fs.LU),
         (16#22F#,16#22F#,Fs.LL),(16#230#,16#230#,Fs.LU),(16#231#,16#231#,Fs.LL),
         (16#232#,16#232#,Fs.LU),(16#233#,16#239#,Fs.LL),(16#23A#,16#23B#,Fs.LU),
         (16#23C#,16#23C#,Fs.LL),(16#23D#,16#23E#,Fs.LU),(16#23F#,16#240#,Fs.LL),
         (16#241#,16#241#,Fs.LU),(16#242#,16#242#,Fs.LL),(16#243#,16#246#,Fs.LU),
         (16#247#,16#247#,Fs.LL),(16#248#,16#248#,Fs.LU),(16#249#,16#249#,Fs.LL),
         (16#24A#,16#24A#,Fs.LU),(16#24B#,16#24B#,Fs.LL),(16#24C#,16#24C#,Fs.LU),
         (16#24D#,16#24D#,Fs.LL),(16#24E#,16#24E#,Fs.LU),(16#24F#,16#293#,Fs.LL),
         (16#294#,16#294#,Fs.LO),(16#295#,16#2AF#,Fs.LL),(16#2B0#,16#2C1#,Fs.LM),
         (16#2C2#,16#2C5#,Fs.SK),(16#2C6#,16#2D1#,Fs.LM),(16#2D2#,16#2DF#,Fs.SK),
         (16#2E0#,16#2E4#,Fs.LM),(16#2E5#,16#2ED#,Fs.SK),(16#2EE#,16#2EE#,Fs.LM),
         (16#2EF#,16#2FF#,Fs.SK),(16#300#,16#36F#,Fs.MN),(16#374#,16#375#,Fs.SK),
         (16#37A#,16#37A#,Fs.LM),(16#37B#,16#37D#,Fs.LL),(16#37E#,16#37E#,Fs.PO),
         (16#384#,16#385#,Fs.SK),(16#386#,16#386#,Fs.LU),(16#387#,16#387#,Fs.PO),
         (16#388#,16#38A#,Fs.LU),(16#38C#,16#38C#,Fs.LU),(16#38E#,16#38F#,Fs.LU),
         (16#390#,16#390#,Fs.LL),(16#391#,16#3A1#,Fs.LU),(16#3A3#,16#3AB#,Fs.LU),
         (16#3AC#,16#3CE#,Fs.LL),(16#3D0#,16#3D1#,Fs.LL),(16#3D2#,16#3D4#,Fs.LU),
         (16#3D5#,16#3D7#,Fs.LL),(16#3D8#,16#3D8#,Fs.LU),(16#3D9#,16#3D9#,Fs.LL),
         (16#3DA#,16#3DA#,Fs.LU),(16#3DB#,16#3DB#,Fs.LL),(16#3DC#,16#3DC#,Fs.LU),
         (16#3DD#,16#3DD#,Fs.LL),(16#3DE#,16#3DE#,Fs.LU),(16#3DF#,16#3DF#,Fs.LL),
         (16#3E0#,16#3E0#,Fs.LU),(16#3E1#,16#3E1#,Fs.LL),(16#3E2#,16#3E2#,Fs.LU),
         (16#3E3#,16#3E3#,Fs.LL),(16#3E4#,16#3E4#,Fs.LU),(16#3E5#,16#3E5#,Fs.LL),
         (16#3E6#,16#3E6#,Fs.LU),(16#3E7#,16#3E7#,Fs.LL),(16#3E8#,16#3E8#,Fs.LU),
         (16#3E9#,16#3E9#,Fs.LL),(16#3EA#,16#3EA#,Fs.LU),(16#3EB#,16#3EB#,Fs.LL),
         (16#3EC#,16#3EC#,Fs.LU),(16#3ED#,16#3ED#,Fs.LL),(16#3EE#,16#3EE#,Fs.LU),
         (16#3EF#,16#3F3#,Fs.LL),(16#3F4#,16#3F4#,Fs.LU),(16#3F5#,16#3F5#,Fs.LL),
         (16#3F6#,16#3F6#,Fs.SM),(16#3F7#,16#3F7#,Fs.LU),(16#3F8#,16#3F8#,Fs.LL),
         (16#3F9#,16#3FA#,Fs.LU),(16#3FB#,16#3FC#,Fs.LL),(16#3FD#,16#42F#,Fs.LU),
         (16#430#,16#45F#,Fs.LL),(16#460#,16#460#,Fs.LU),(16#461#,16#461#,Fs.LL),
         (16#462#,16#462#,Fs.LU),(16#463#,16#463#,Fs.LL),(16#464#,16#464#,Fs.LU),
         (16#465#,16#465#,Fs.LL),(16#466#,16#466#,Fs.LU),(16#467#,16#467#,Fs.LL),
         (16#468#,16#468#,Fs.LU),(16#469#,16#469#,Fs.LL),(16#46A#,16#46A#,Fs.LU),
         (16#46B#,16#46B#,Fs.LL),(16#46C#,16#46C#,Fs.LU),(16#46D#,16#46D#,Fs.LL),
         (16#46E#,16#46E#,Fs.LU),(16#46F#,16#46F#,Fs.LL),(16#470#,16#470#,Fs.LU),
         (16#471#,16#471#,Fs.LL),(16#472#,16#472#,Fs.LU),(16#473#,16#473#,Fs.LL),
         (16#474#,16#474#,Fs.LU),(16#475#,16#475#,Fs.LL),(16#476#,16#476#,Fs.LU),
         (16#477#,16#477#,Fs.LL),(16#478#,16#478#,Fs.LU),(16#479#,16#479#,Fs.LL),
         (16#47A#,16#47A#,Fs.LU),(16#47B#,16#47B#,Fs.LL),(16#47C#,16#47C#,Fs.LU),
         (16#47D#,16#47D#,Fs.LL),(16#47E#,16#47E#,Fs.LU),(16#47F#,16#47F#,Fs.LL),
         (16#480#,16#480#,Fs.LU),(16#481#,16#481#,Fs.LL),(16#482#,16#482#,Fs.SO),
         (16#483#,16#486#,Fs.MN),(16#488#,16#489#,Fs.ME),(16#48A#,16#48A#,Fs.LU),
         (16#48B#,16#48B#,Fs.LL),(16#48C#,16#48C#,Fs.LU),(16#48D#,16#48D#,Fs.LL),
         (16#48E#,16#48E#,Fs.LU),(16#48F#,16#48F#,Fs.LL),(16#490#,16#490#,Fs.LU),
         (16#491#,16#491#,Fs.LL),(16#492#,16#492#,Fs.LU),(16#493#,16#493#,Fs.LL),
         (16#494#,16#494#,Fs.LU),(16#495#,16#495#,Fs.LL),(16#496#,16#496#,Fs.LU),
         (16#497#,16#497#,Fs.LL),(16#498#,16#498#,Fs.LU),(16#499#,16#499#,Fs.LL),
         (16#49A#,16#49A#,Fs.LU),(16#49B#,16#49B#,Fs.LL),(16#49C#,16#49C#,Fs.LU),
         (16#49D#,16#49D#,Fs.LL),(16#49E#,16#49E#,Fs.LU),(16#49F#,16#49F#,Fs.LL),
         (16#4A0#,16#4A0#,Fs.LU),(16#4A1#,16#4A1#,Fs.LL),(16#4A2#,16#4A2#,Fs.LU),
         (16#4A3#,16#4A3#,Fs.LL),(16#4A4#,16#4A4#,Fs.LU),(16#4A5#,16#4A5#,Fs.LL),
         (16#4A6#,16#4A6#,Fs.LU),(16#4A7#,16#4A7#,Fs.LL),(16#4A8#,16#4A8#,Fs.LU),
         (16#4A9#,16#4A9#,Fs.LL),(16#4AA#,16#4AA#,Fs.LU),(16#4AB#,16#4AB#,Fs.LL),
         (16#4AC#,16#4AC#,Fs.LU),(16#4AD#,16#4AD#,Fs.LL),(16#4AE#,16#4AE#,Fs.LU),
         (16#4AF#,16#4AF#,Fs.LL),(16#4B0#,16#4B0#,Fs.LU),(16#4B1#,16#4B1#,Fs.LL),
         (16#4B2#,16#4B2#,Fs.LU),(16#4B3#,16#4B3#,Fs.LL),(16#4B4#,16#4B4#,Fs.LU),
         (16#4B5#,16#4B5#,Fs.LL),(16#4B6#,16#4B6#,Fs.LU),(16#4B7#,16#4B7#,Fs.LL),
         (16#4B8#,16#4B8#,Fs.LU),(16#4B9#,16#4B9#,Fs.LL),(16#4BA#,16#4BA#,Fs.LU),
         (16#4BB#,16#4BB#,Fs.LL),(16#4BC#,16#4BC#,Fs.LU),(16#4BD#,16#4BD#,Fs.LL),
         (16#4BE#,16#4BE#,Fs.LU),(16#4BF#,16#4BF#,Fs.LL),(16#4C0#,16#4C1#,Fs.LU),
         (16#4C2#,16#4C2#,Fs.LL),(16#4C3#,16#4C3#,Fs.LU),(16#4C4#,16#4C4#,Fs.LL),
         (16#4C5#,16#4C5#,Fs.LU),(16#4C6#,16#4C6#,Fs.LL),(16#4C7#,16#4C7#,Fs.LU),
         (16#4C8#,16#4C8#,Fs.LL),(16#4C9#,16#4C9#,Fs.LU),(16#4CA#,16#4CA#,Fs.LL),
         (16#4CB#,16#4CB#,Fs.LU),(16#4CC#,16#4CC#,Fs.LL),(16#4CD#,16#4CD#,Fs.LU),
         (16#4CE#,16#4CF#,Fs.LL),(16#4D0#,16#4D0#,Fs.LU),(16#4D1#,16#4D1#,Fs.LL),
         (16#4D2#,16#4D2#,Fs.LU),(16#4D3#,16#4D3#,Fs.LL),(16#4D4#,16#4D4#,Fs.LU),
         (16#4D5#,16#4D5#,Fs.LL),(16#4D6#,16#4D6#,Fs.LU),(16#4D7#,16#4D7#,Fs.LL),
         (16#4D8#,16#4D8#,Fs.LU),(16#4D9#,16#4D9#,Fs.LL),(16#4DA#,16#4DA#,Fs.LU),
         (16#4DB#,16#4DB#,Fs.LL),(16#4DC#,16#4DC#,Fs.LU),(16#4DD#,16#4DD#,Fs.LL),
         (16#4DE#,16#4DE#,Fs.LU),(16#4DF#,16#4DF#,Fs.LL),(16#4E0#,16#4E0#,Fs.LU),
         (16#4E1#,16#4E1#,Fs.LL),(16#4E2#,16#4E2#,Fs.LU),(16#4E3#,16#4E3#,Fs.LL),
         (16#4E4#,16#4E4#,Fs.LU),(16#4E5#,16#4E5#,Fs.LL),(16#4E6#,16#4E6#,Fs.LU),
         (16#4E7#,16#4E7#,Fs.LL),(16#4E8#,16#4E8#,Fs.LU),(16#4E9#,16#4E9#,Fs.LL),
         (16#4EA#,16#4EA#,Fs.LU),(16#4EB#,16#4EB#,Fs.LL),(16#4EC#,16#4EC#,Fs.LU),
         (16#4ED#,16#4ED#,Fs.LL),(16#4EE#,16#4EE#,Fs.LU),(16#4EF#,16#4EF#,Fs.LL),
         (16#4F0#,16#4F0#,Fs.LU),(16#4F1#,16#4F1#,Fs.LL),(16#4F2#,16#4F2#,Fs.LU),
         (16#4F3#,16#4F3#,Fs.LL),(16#4F4#,16#4F4#,Fs.LU),(16#4F5#,16#4F5#,Fs.LL),
         (16#4F6#,16#4F6#,Fs.LU),(16#4F7#,16#4F7#,Fs.LL),(16#4F8#,16#4F8#,Fs.LU),
         (16#4F9#,16#4F9#,Fs.LL),(16#4FA#,16#4FA#,Fs.LU),(16#4FB#,16#4FB#,Fs.LL),
         (16#4FC#,16#4FC#,Fs.LU),(16#4FD#,16#4FD#,Fs.LL),(16#4FE#,16#4FE#,Fs.LU),
         (16#4FF#,16#4FF#,Fs.LL),(16#500#,16#500#,Fs.LU),(16#501#,16#501#,Fs.LL),
         (16#502#,16#502#,Fs.LU),(16#503#,16#503#,Fs.LL),(16#504#,16#504#,Fs.LU),
         (16#505#,16#505#,Fs.LL),(16#506#,16#506#,Fs.LU),(16#507#,16#507#,Fs.LL),
         (16#508#,16#508#,Fs.LU),(16#509#,16#509#,Fs.LL),(16#50A#,16#50A#,Fs.LU),
         (16#50B#,16#50B#,Fs.LL),(16#50C#,16#50C#,Fs.LU),(16#50D#,16#50D#,Fs.LL),
         (16#50E#,16#50E#,Fs.LU),(16#50F#,16#50F#,Fs.LL),(16#510#,16#510#,Fs.LU),
         (16#511#,16#511#,Fs.LL),(16#512#,16#512#,Fs.LU),(16#513#,16#513#,Fs.LL),
         (16#531#,16#556#,Fs.LU),(16#559#,16#559#,Fs.LM),(16#55A#,16#55F#,Fs.PO),
         (16#561#,16#587#,Fs.LL),(16#589#,16#589#,Fs.PO),(16#58A#,16#58A#,Fs.PD),
         (16#591#,16#5BD#,Fs.MN),(16#5BE#,16#5BE#,Fs.PO),(16#5BF#,16#5BF#,Fs.MN),
         (16#5C0#,16#5C0#,Fs.PO),(16#5C1#,16#5C2#,Fs.MN),(16#5C3#,16#5C3#,Fs.PO),
         (16#5C4#,16#5C5#,Fs.MN),(16#5C6#,16#5C6#,Fs.PO),(16#5C7#,16#5C7#,Fs.MN),
         (16#5D0#,16#5EA#,Fs.LO),(16#5F0#,16#5F2#,Fs.LO),(16#5F3#,16#5F4#,Fs.PO),
         (16#600#,16#603#,Fs.CF),(16#60B#,16#60B#,Fs.SC),(16#60C#,16#60D#,Fs.PO),
         (16#60E#,16#60F#,Fs.SO),(16#610#,16#615#,Fs.MN),(16#61B#,16#61B#,Fs.PO),
         (16#61E#,16#61F#,Fs.PO),(16#621#,16#63A#,Fs.LO),(16#640#,16#640#,Fs.LM),
         (16#641#,16#64A#,Fs.LO),(16#64B#,16#65E#,Fs.MN),(16#660#,16#669#,Fs.ND),
         (16#66A#,16#66D#,Fs.PO),(16#66E#,16#66F#,Fs.LO),(16#670#,16#670#,Fs.MN),
         (16#671#,16#6D3#,Fs.LO),(16#6D4#,16#6D4#,Fs.PO),(16#6D5#,16#6D5#,Fs.LO),
         (16#6D6#,16#6DC#,Fs.MN),(16#6DD#,16#6DD#,Fs.CF),(16#6DE#,16#6DE#,Fs.ME),
         (16#6DF#,16#6E4#,Fs.MN),(16#6E5#,16#6E6#,Fs.LM),(16#6E7#,16#6E8#,Fs.MN),
         (16#6E9#,16#6E9#,Fs.SO),(16#6EA#,16#6ED#,Fs.MN),(16#6EE#,16#6EF#,Fs.LO),
         (16#6F0#,16#6F9#,Fs.ND),(16#6FA#,16#6FC#,Fs.LO),(16#6FD#,16#6FE#,Fs.SO),
         (16#6FF#,16#6FF#,Fs.LO),(16#700#,16#70D#,Fs.PO),(16#70F#,16#70F#,Fs.CF),
         (16#710#,16#710#,Fs.LO),(16#711#,16#711#,Fs.MN),(16#712#,16#72F#,Fs.LO),
         (16#730#,16#74A#,Fs.MN),(16#74D#,16#76D#,Fs.LO),(16#780#,16#7A5#,Fs.LO),
         (16#7A6#,16#7B0#,Fs.MN),(16#7B1#,16#7B1#,Fs.LO),(16#7C0#,16#7C9#,Fs.ND),
         (16#7CA#,16#7EA#,Fs.LO),(16#7EB#,16#7F3#,Fs.MN),(16#7F4#,16#7F5#,Fs.LM),
         (16#7F6#,16#7F6#,Fs.SO),(16#7F7#,16#7F9#,Fs.PO),(16#7FA#,16#7FA#,Fs.LM),
         (16#901#,16#902#,Fs.MN),(16#903#,16#903#,Fs.MC),(16#904#,16#939#,Fs.LO),
         (16#93C#,16#93C#,Fs.MN),(16#93D#,16#93D#,Fs.LO),(16#93E#,16#940#,Fs.MC),
         (16#941#,16#948#,Fs.MN),(16#949#,16#94C#,Fs.MC),(16#94D#,16#94D#,Fs.MN),
         (16#950#,16#950#,Fs.LO),(16#951#,16#954#,Fs.MN),(16#958#,16#961#,Fs.LO),
         (16#962#,16#963#,Fs.MN),(16#964#,16#965#,Fs.PO),(16#966#,16#96F#,Fs.ND),
         (16#970#,16#970#,Fs.PO),(16#97B#,16#97F#,Fs.LO),(16#981#,16#981#,Fs.MN),
         (16#982#,16#983#,Fs.MC),(16#985#,16#98C#,Fs.LO),(16#98F#,16#990#,Fs.LO),
         (16#993#,16#9A8#,Fs.LO),(16#9AA#,16#9B0#,Fs.LO),(16#9B2#,16#9B2#,Fs.LO),
         (16#9B6#,16#9B9#,Fs.LO),(16#9BC#,16#9BC#,Fs.MN),(16#9BD#,16#9BD#,Fs.LO),
         (16#9BE#,16#9C0#,Fs.MC),(16#9C1#,16#9C4#,Fs.MN),(16#9C7#,16#9C8#,Fs.MC),
         (16#9CB#,16#9CC#,Fs.MC),(16#9CD#,16#9CD#,Fs.MN),(16#9CE#,16#9CE#,Fs.LO),
         (16#9D7#,16#9D7#,Fs.MC),(16#9DC#,16#9DD#,Fs.LO),(16#9DF#,16#9E1#,Fs.LO),
         (16#9E2#,16#9E3#,Fs.MN),(16#9E6#,16#9EF#,Fs.ND),(16#9F0#,16#9F1#,Fs.LO),
         (16#9F2#,16#9F3#,Fs.SC),(16#9F4#,16#9F9#,Fs.NO),(16#9FA#,16#9FA#,Fs.SO),
         (16#A01#,16#A02#,Fs.MN),(16#A03#,16#A03#,Fs.MC),(16#A05#,16#A0A#,Fs.LO),
         (16#A0F#,16#A10#,Fs.LO),(16#A13#,16#A28#,Fs.LO),(16#A2A#,16#A30#,Fs.LO),
         (16#A32#,16#A33#,Fs.LO),(16#A35#,16#A36#,Fs.LO),(16#A38#,16#A39#,Fs.LO),
         (16#A3C#,16#A3C#,Fs.MN),(16#A3E#,16#A40#,Fs.MC),(16#A41#,16#A42#,Fs.MN),
         (16#A47#,16#A48#,Fs.MN),(16#A4B#,16#A4D#,Fs.MN),(16#A59#,16#A5C#,Fs.LO),
         (16#A5E#,16#A5E#,Fs.LO),(16#A66#,16#A6F#,Fs.ND),(16#A70#,16#A71#,Fs.MN),
         (16#A72#,16#A74#,Fs.LO),(16#A81#,16#A82#,Fs.MN),(16#A83#,16#A83#,Fs.MC),
         (16#A85#,16#A8D#,Fs.LO),(16#A8F#,16#A91#,Fs.LO),(16#A93#,16#AA8#,Fs.LO),
         (16#AAA#,16#AB0#,Fs.LO),(16#AB2#,16#AB3#,Fs.LO),(16#AB5#,16#AB9#,Fs.LO),
         (16#ABC#,16#ABC#,Fs.MN),(16#ABD#,16#ABD#,Fs.LO),(16#ABE#,16#AC0#,Fs.MC),
         (16#AC1#,16#AC5#,Fs.MN),(16#AC7#,16#AC8#,Fs.MN),(16#AC9#,16#AC9#,Fs.MC),
         (16#ACB#,16#ACC#,Fs.MC),(16#ACD#,16#ACD#,Fs.MN),(16#AD0#,16#AD0#,Fs.LO),
         (16#AE0#,16#AE1#,Fs.LO),(16#AE2#,16#AE3#,Fs.MN),(16#AE6#,16#AEF#,Fs.ND),
         (16#AF1#,16#AF1#,Fs.SC),(16#B01#,16#B01#,Fs.MN),(16#B02#,16#B03#,Fs.MC),
         (16#B05#,16#B0C#,Fs.LO),(16#B0F#,16#B10#,Fs.LO),(16#B13#,16#B28#,Fs.LO),
         (16#B2A#,16#B30#,Fs.LO),(16#B32#,16#B33#,Fs.LO),(16#B35#,16#B39#,Fs.LO),
         (16#B3C#,16#B3C#,Fs.MN),(16#B3D#,16#B3D#,Fs.LO),(16#B3E#,16#B3E#,Fs.MC),
         (16#B3F#,16#B3F#,Fs.MN),(16#B40#,16#B40#,Fs.MC),(16#B41#,16#B43#,Fs.MN),
         (16#B47#,16#B48#,Fs.MC),(16#B4B#,16#B4C#,Fs.MC),(16#B4D#,16#B4D#,Fs.MN),
         (16#B56#,16#B56#,Fs.MN),(16#B57#,16#B57#,Fs.MC),(16#B5C#,16#B5D#,Fs.LO),
         (16#B5F#,16#B61#,Fs.LO),(16#B66#,16#B6F#,Fs.ND),(16#B70#,16#B70#,Fs.SO),
         (16#B71#,16#B71#,Fs.LO),(16#B82#,16#B82#,Fs.MN),(16#B83#,16#B83#,Fs.LO),
         (16#B85#,16#B8A#,Fs.LO),(16#B8E#,16#B90#,Fs.LO),(16#B92#,16#B95#,Fs.LO),
         (16#B99#,16#B9A#,Fs.LO),(16#B9C#,16#B9C#,Fs.LO),(16#B9E#,16#B9F#,Fs.LO),
         (16#BA3#,16#BA4#,Fs.LO),(16#BA8#,16#BAA#,Fs.LO),(16#BAE#,16#BB9#,Fs.LO),
         (16#BBE#,16#BBF#,Fs.MC),(16#BC0#,16#BC0#,Fs.MN),(16#BC1#,16#BC2#,Fs.MC),
         (16#BC6#,16#BC8#,Fs.MC),(16#BCA#,16#BCC#,Fs.MC),(16#BCD#,16#BCD#,Fs.MN),
         (16#BD7#,16#BD7#,Fs.MC),(16#BE6#,16#BEF#,Fs.ND),(16#BF0#,16#BF2#,Fs.NO),
         (16#BF3#,16#BF8#,Fs.SO),(16#BF9#,16#BF9#,Fs.SC),(16#BFA#,16#BFA#,Fs.SO),
         (16#C01#,16#C03#,Fs.MC),(16#C05#,16#C0C#,Fs.LO),(16#C0E#,16#C10#,Fs.LO),
         (16#C12#,16#C28#,Fs.LO),(16#C2A#,16#C33#,Fs.LO),(16#C35#,16#C39#,Fs.LO),
         (16#C3E#,16#C40#,Fs.MN),(16#C41#,16#C44#,Fs.MC),(16#C46#,16#C48#,Fs.MN),
         (16#C4A#,16#C4D#,Fs.MN),(16#C55#,16#C56#,Fs.MN),(16#C60#,16#C61#,Fs.LO),
         (16#C66#,16#C6F#,Fs.ND),(16#C82#,16#C83#,Fs.MC),(16#C85#,16#C8C#,Fs.LO),
         (16#C8E#,16#C90#,Fs.LO),(16#C92#,16#CA8#,Fs.LO),(16#CAA#,16#CB3#,Fs.LO),
         (16#CB5#,16#CB9#,Fs.LO),(16#CBC#,16#CBC#,Fs.MN),(16#CBD#,16#CBD#,Fs.LO),
         (16#CBE#,16#CBE#,Fs.MC),(16#CBF#,16#CBF#,Fs.MN),(16#CC0#,16#CC4#,Fs.MC),
         (16#CC6#,16#CC6#,Fs.MN),(16#CC7#,16#CC8#,Fs.MC),(16#CCA#,16#CCB#,Fs.MC),
         (16#CCC#,16#CCD#,Fs.MN),(16#CD5#,16#CD6#,Fs.MC),(16#CDE#,16#CDE#,Fs.LO),
         (16#CE0#,16#CE1#,Fs.LO),(16#CE2#,16#CE3#,Fs.MN),(16#CE6#,16#CEF#,Fs.ND),
         (16#CF1#,16#CF2#,Fs.SO),(16#D02#,16#D03#,Fs.MC),(16#D05#,16#D0C#,Fs.LO),
         (16#D0E#,16#D10#,Fs.LO),(16#D12#,16#D28#,Fs.LO),(16#D2A#,16#D39#,Fs.LO),
         (16#D3E#,16#D40#,Fs.MC),(16#D41#,16#D43#,Fs.MN),(16#D46#,16#D48#,Fs.MC),
         (16#D4A#,16#D4C#,Fs.MC),(16#D4D#,16#D4D#,Fs.MN),(16#D57#,16#D57#,Fs.MC),
         (16#D60#,16#D61#,Fs.LO),(16#D66#,16#D6F#,Fs.ND),(16#D82#,16#D83#,Fs.MC),
         (16#D85#,16#D96#,Fs.LO),(16#D9A#,16#DB1#,Fs.LO),(16#DB3#,16#DBB#,Fs.LO),
         (16#DBD#,16#DBD#,Fs.LO),(16#DC0#,16#DC6#,Fs.LO),(16#DCA#,16#DCA#,Fs.MN),
         (16#DCF#,16#DD1#,Fs.MC),(16#DD2#,16#DD4#,Fs.MN),(16#DD6#,16#DD6#,Fs.MN),
         (16#DD8#,16#DDF#,Fs.MC),(16#DF2#,16#DF3#,Fs.MC),(16#DF4#,16#DF4#,Fs.PO),
         (16#E01#,16#E30#,Fs.LO),(16#E31#,16#E31#,Fs.MN),(16#E32#,16#E33#,Fs.LO),
         (16#E34#,16#E3A#,Fs.MN),(16#E3F#,16#E3F#,Fs.SC),(16#E40#,16#E45#,Fs.LO),
         (16#E46#,16#E46#,Fs.LM),(16#E47#,16#E4E#,Fs.MN),(16#E4F#,16#E4F#,Fs.PO),
         (16#E50#,16#E59#,Fs.ND),(16#E5A#,16#E5B#,Fs.PO),(16#E81#,16#E82#,Fs.LO),
         (16#E84#,16#E84#,Fs.LO),(16#E87#,16#E88#,Fs.LO),(16#E8A#,16#E8A#,Fs.LO),
         (16#E8D#,16#E8D#,Fs.LO),(16#E94#,16#E97#,Fs.LO),(16#E99#,16#E9F#,Fs.LO),
         (16#EA1#,16#EA3#,Fs.LO),(16#EA5#,16#EA5#,Fs.LO),(16#EA7#,16#EA7#,Fs.LO),
         (16#EAA#,16#EAB#,Fs.LO),(16#EAD#,16#EB0#,Fs.LO),(16#EB1#,16#EB1#,Fs.MN),
         (16#EB2#,16#EB3#,Fs.LO),(16#EB4#,16#EB9#,Fs.MN),(16#EBB#,16#EBC#,Fs.MN),
         (16#EBD#,16#EBD#,Fs.LO),(16#EC0#,16#EC4#,Fs.LO),(16#EC6#,16#EC6#,Fs.LM),
         (16#EC8#,16#ECD#,Fs.MN),(16#ED0#,16#ED9#,Fs.ND),(16#EDC#,16#EDD#,Fs.LO),
         (16#F00#,16#F00#,Fs.LO),(16#F01#,16#F03#,Fs.SO),(16#F04#,16#F12#,Fs.PO),
         (16#F13#,16#F17#,Fs.SO),(16#F18#,16#F19#,Fs.MN),(16#F1A#,16#F1F#,Fs.SO),
         (16#F20#,16#F29#,Fs.ND),(16#F2A#,16#F33#,Fs.NO),(16#F34#,16#F34#,Fs.SO),
         (16#F35#,16#F35#,Fs.MN),(16#F36#,16#F36#,Fs.SO),(16#F37#,16#F37#,Fs.MN),
         (16#F38#,16#F38#,Fs.SO),(16#F39#,16#F39#,Fs.MN),(16#F3A#,16#F3A#,Fs.PS),
         (16#F3B#,16#F3B#,Fs.PE),(16#F3C#,16#F3C#,Fs.PS),(16#F3D#,16#F3D#,Fs.PE),
         (16#F3E#,16#F3F#,Fs.MC),(16#F40#,16#F47#,Fs.LO),(16#F49#,16#F6A#,Fs.LO),
         (16#F71#,16#F7E#,Fs.MN),(16#F7F#,16#F7F#,Fs.MC),(16#F80#,16#F84#,Fs.MN),
         (16#F85#,16#F85#,Fs.PO),(16#F86#,16#F87#,Fs.MN),(16#F88#,16#F8B#,Fs.LO),
         (16#F90#,16#F97#,Fs.MN),(16#F99#,16#FBC#,Fs.MN),(16#FBE#,16#FC5#,Fs.SO),
         (16#FC6#,16#FC6#,Fs.MN),(16#FC7#,16#FCC#,Fs.SO),(16#FCF#,16#FCF#,Fs.SO),
         (16#FD0#,16#FD1#,Fs.PO),(16#1000#,16#1021#,Fs.LO),(16#1023#,16#1027#,Fs.LO),
         (16#1029#,16#102A#,Fs.LO),(16#102C#,16#102C#,Fs.MC),(16#102D#,16#1030#,Fs.MN),
         (16#1031#,16#1031#,Fs.MC),(16#1032#,16#1032#,Fs.MN),(16#1036#,16#1037#,Fs.MN),
         (16#1038#,16#1038#,Fs.MC),(16#1039#,16#1039#,Fs.MN),(16#1040#,16#1049#,Fs.ND),
         (16#104A#,16#104F#,Fs.PO),(16#1050#,16#1055#,Fs.LO),(16#1056#,16#1057#,Fs.MC),
         (16#1058#,16#1059#,Fs.MN),(16#10A0#,16#10C5#,Fs.LU),(16#10D0#,16#10FA#,Fs.LO),
         (16#10FB#,16#10FB#,Fs.PO),(16#10FC#,16#10FC#,Fs.LM),(16#1100#,16#1159#,Fs.LO),
         (16#115F#,16#11A2#,Fs.LO),(16#11A8#,16#11F9#,Fs.LO),(16#1200#,16#1248#,Fs.LO),
         (16#124A#,16#124D#,Fs.LO),(16#1250#,16#1256#,Fs.LO),(16#1258#,16#1258#,Fs.LO),
         (16#125A#,16#125D#,Fs.LO),(16#1260#,16#1288#,Fs.LO),(16#128A#,16#128D#,Fs.LO),
         (16#1290#,16#12B0#,Fs.LO),(16#12B2#,16#12B5#,Fs.LO),(16#12B8#,16#12BE#,Fs.LO),
         (16#12C0#,16#12C0#,Fs.LO),(16#12C2#,16#12C5#,Fs.LO),(16#12C8#,16#12D6#,Fs.LO),
         (16#12D8#,16#1310#,Fs.LO),(16#1312#,16#1315#,Fs.LO),(16#1318#,16#135A#,Fs.LO),
         (16#135F#,16#135F#,Fs.MN),(16#1360#,16#1360#,Fs.SO),(16#1361#,16#1368#,Fs.PO),
         (16#1369#,16#137C#,Fs.NO),(16#1380#,16#138F#,Fs.LO),(16#1390#,16#1399#,Fs.SO),
         (16#13A0#,16#13F4#,Fs.LO),(16#1401#,16#166C#,Fs.LO),(16#166D#,16#166E#,Fs.PO),
         (16#166F#,16#1676#,Fs.LO),(16#1680#,16#1680#,Fs.ZS),(16#1681#,16#169A#,Fs.LO),
         (16#169B#,16#169B#,Fs.PS),(16#169C#,16#169C#,Fs.PE),(16#16A0#,16#16EA#,Fs.LO),
         (16#16EB#,16#16ED#,Fs.PO),(16#16EE#,16#16F0#,Fs.NL),(16#1700#,16#170C#,Fs.LO),
         (16#170E#,16#1711#,Fs.LO),(16#1712#,16#1714#,Fs.MN),(16#1720#,16#1731#,Fs.LO),
         (16#1732#,16#1734#,Fs.MN),(16#1735#,16#1736#,Fs.PO),(16#1740#,16#1751#,Fs.LO),
         (16#1752#,16#1753#,Fs.MN),(16#1760#,16#176C#,Fs.LO),(16#176E#,16#1770#,Fs.LO),
         (16#1772#,16#1773#,Fs.MN),(16#1780#,16#17B3#,Fs.LO),(16#17B4#,16#17B5#,Fs.CF),
         (16#17B6#,16#17B6#,Fs.MC),(16#17B7#,16#17BD#,Fs.MN),(16#17BE#,16#17C5#,Fs.MC),
         (16#17C6#,16#17C6#,Fs.MN),(16#17C7#,16#17C8#,Fs.MC),(16#17C9#,16#17D3#,Fs.MN),
         (16#17D4#,16#17D6#,Fs.PO),(16#17D7#,16#17D7#,Fs.LM),(16#17D8#,16#17DA#,Fs.PO),
         (16#17DB#,16#17DB#,Fs.SC),(16#17DC#,16#17DC#,Fs.LO),(16#17DD#,16#17DD#,Fs.MN),
         (16#17E0#,16#17E9#,Fs.ND),(16#17F0#,16#17F9#,Fs.NO),(16#1800#,16#1805#,Fs.PO),
         (16#1806#,16#1806#,Fs.PD),(16#1807#,16#180A#,Fs.PO),(16#180B#,16#180D#,Fs.MN),
         (16#180E#,16#180E#,Fs.ZS),(16#1810#,16#1819#,Fs.ND),(16#1820#,16#1842#,Fs.LO),
         (16#1843#,16#1843#,Fs.LM),(16#1844#,16#1877#,Fs.LO),(16#1880#,16#18A8#,Fs.LO),
         (16#18A9#,16#18A9#,Fs.MN),(16#1900#,16#191C#,Fs.LO),(16#1920#,16#1922#,Fs.MN),
         (16#1923#,16#1926#,Fs.MC),(16#1927#,16#1928#,Fs.MN),(16#1929#,16#192B#,Fs.MC),
         (16#1930#,16#1931#,Fs.MC),(16#1932#,16#1932#,Fs.MN),(16#1933#,16#1938#,Fs.MC),
         (16#1939#,16#193B#,Fs.MN),(16#1940#,16#1940#,Fs.SO),(16#1944#,16#1945#,Fs.PO),
         (16#1946#,16#194F#,Fs.ND),(16#1950#,16#196D#,Fs.LO),(16#1970#,16#1974#,Fs.LO),
         (16#1980#,16#19A9#,Fs.LO),(16#19B0#,16#19C0#,Fs.MC),(16#19C1#,16#19C7#,Fs.LO),
         (16#19C8#,16#19C9#,Fs.MC),(16#19D0#,16#19D9#,Fs.ND),(16#19DE#,16#19DF#,Fs.PO),
         (16#19E0#,16#19FF#,Fs.SO),(16#1A00#,16#1A16#,Fs.LO),(16#1A17#,16#1A18#,Fs.MN),
         (16#1A19#,16#1A1B#,Fs.MC),(16#1A1E#,16#1A1F#,Fs.PO),(16#1B00#,16#1B03#,Fs.MN),
         (16#1B04#,16#1B04#,Fs.MC),(16#1B05#,16#1B33#,Fs.LO),(16#1B34#,16#1B34#,Fs.MN),
         (16#1B35#,16#1B35#,Fs.MC),(16#1B36#,16#1B3A#,Fs.MN),(16#1B3B#,16#1B3B#,Fs.MC),
         (16#1B3C#,16#1B3C#,Fs.MN),(16#1B3D#,16#1B41#,Fs.MC),(16#1B42#,16#1B42#,Fs.MN),
         (16#1B43#,16#1B44#,Fs.MC),(16#1B45#,16#1B4B#,Fs.LO),(16#1B50#,16#1B59#,Fs.ND),
         (16#1B5A#,16#1B60#,Fs.PO),(16#1B61#,16#1B6A#,Fs.SO),(16#1B6B#,16#1B73#,Fs.MN),
         (16#1B74#,16#1B7C#,Fs.SO),(16#1D00#,16#1D2B#,Fs.LL),(16#1D2C#,16#1D61#,Fs.LM),
         (16#1D62#,16#1D77#,Fs.LL),(16#1D78#,16#1D78#,Fs.LM),(16#1D79#,16#1D9A#,Fs.LL),
         (16#1D9B#,16#1DBF#,Fs.LM),(16#1DC0#,16#1DCA#,Fs.MN),(16#1DFE#,16#1DFF#,Fs.MN),
         (16#1E00#,16#1E00#,Fs.LU),(16#1E01#,16#1E01#,Fs.LL),(16#1E02#,16#1E02#,Fs.LU),
         (16#1E03#,16#1E03#,Fs.LL),(16#1E04#,16#1E04#,Fs.LU),(16#1E05#,16#1E05#,Fs.LL),
         (16#1E06#,16#1E06#,Fs.LU),(16#1E07#,16#1E07#,Fs.LL),(16#1E08#,16#1E08#,Fs.LU),
         (16#1E09#,16#1E09#,Fs.LL),(16#1E0A#,16#1E0A#,Fs.LU),(16#1E0B#,16#1E0B#,Fs.LL),
         (16#1E0C#,16#1E0C#,Fs.LU),(16#1E0D#,16#1E0D#,Fs.LL),(16#1E0E#,16#1E0E#,Fs.LU),
         (16#1E0F#,16#1E0F#,Fs.LL),(16#1E10#,16#1E10#,Fs.LU),(16#1E11#,16#1E11#,Fs.LL),
         (16#1E12#,16#1E12#,Fs.LU),(16#1E13#,16#1E13#,Fs.LL),(16#1E14#,16#1E14#,Fs.LU),
         (16#1E15#,16#1E15#,Fs.LL),(16#1E16#,16#1E16#,Fs.LU),(16#1E17#,16#1E17#,Fs.LL),
         (16#1E18#,16#1E18#,Fs.LU),(16#1E19#,16#1E19#,Fs.LL),(16#1E1A#,16#1E1A#,Fs.LU),
         (16#1E1B#,16#1E1B#,Fs.LL),(16#1E1C#,16#1E1C#,Fs.LU),(16#1E1D#,16#1E1D#,Fs.LL),
         (16#1E1E#,16#1E1E#,Fs.LU),(16#1E1F#,16#1E1F#,Fs.LL),(16#1E20#,16#1E20#,Fs.LU),
         (16#1E21#,16#1E21#,Fs.LL),(16#1E22#,16#1E22#,Fs.LU),(16#1E23#,16#1E23#,Fs.LL),
         (16#1E24#,16#1E24#,Fs.LU),(16#1E25#,16#1E25#,Fs.LL),(16#1E26#,16#1E26#,Fs.LU),
         (16#1E27#,16#1E27#,Fs.LL),(16#1E28#,16#1E28#,Fs.LU),(16#1E29#,16#1E29#,Fs.LL),
         (16#1E2A#,16#1E2A#,Fs.LU),(16#1E2B#,16#1E2B#,Fs.LL),(16#1E2C#,16#1E2C#,Fs.LU),
         (16#1E2D#,16#1E2D#,Fs.LL),(16#1E2E#,16#1E2E#,Fs.LU),(16#1E2F#,16#1E2F#,Fs.LL),
         (16#1E30#,16#1E30#,Fs.LU),(16#1E31#,16#1E31#,Fs.LL),(16#1E32#,16#1E32#,Fs.LU),
         (16#1E33#,16#1E33#,Fs.LL),(16#1E34#,16#1E34#,Fs.LU),(16#1E35#,16#1E35#,Fs.LL),
         (16#1E36#,16#1E36#,Fs.LU),(16#1E37#,16#1E37#,Fs.LL),(16#1E38#,16#1E38#,Fs.LU),
         (16#1E39#,16#1E39#,Fs.LL),(16#1E3A#,16#1E3A#,Fs.LU),(16#1E3B#,16#1E3B#,Fs.LL),
         (16#1E3C#,16#1E3C#,Fs.LU),(16#1E3D#,16#1E3D#,Fs.LL),(16#1E3E#,16#1E3E#,Fs.LU),
         (16#1E3F#,16#1E3F#,Fs.LL),(16#1E40#,16#1E40#,Fs.LU),(16#1E41#,16#1E41#,Fs.LL),
         (16#1E42#,16#1E42#,Fs.LU),(16#1E43#,16#1E43#,Fs.LL),(16#1E44#,16#1E44#,Fs.LU),
         (16#1E45#,16#1E45#,Fs.LL),(16#1E46#,16#1E46#,Fs.LU),(16#1E47#,16#1E47#,Fs.LL),
         (16#1E48#,16#1E48#,Fs.LU),(16#1E49#,16#1E49#,Fs.LL),(16#1E4A#,16#1E4A#,Fs.LU),
         (16#1E4B#,16#1E4B#,Fs.LL),(16#1E4C#,16#1E4C#,Fs.LU),(16#1E4D#,16#1E4D#,Fs.LL),
         (16#1E4E#,16#1E4E#,Fs.LU),(16#1E4F#,16#1E4F#,Fs.LL),(16#1E50#,16#1E50#,Fs.LU),
         (16#1E51#,16#1E51#,Fs.LL),(16#1E52#,16#1E52#,Fs.LU),(16#1E53#,16#1E53#,Fs.LL),
         (16#1E54#,16#1E54#,Fs.LU),(16#1E55#,16#1E55#,Fs.LL),(16#1E56#,16#1E56#,Fs.LU),
         (16#1E57#,16#1E57#,Fs.LL),(16#1E58#,16#1E58#,Fs.LU),(16#1E59#,16#1E59#,Fs.LL),
         (16#1E5A#,16#1E5A#,Fs.LU),(16#1E5B#,16#1E5B#,Fs.LL),(16#1E5C#,16#1E5C#,Fs.LU),
         (16#1E5D#,16#1E5D#,Fs.LL),(16#1E5E#,16#1E5E#,Fs.LU),(16#1E5F#,16#1E5F#,Fs.LL),
         (16#1E60#,16#1E60#,Fs.LU),(16#1E61#,16#1E61#,Fs.LL),(16#1E62#,16#1E62#,Fs.LU),
         (16#1E63#,16#1E63#,Fs.LL),(16#1E64#,16#1E64#,Fs.LU),(16#1E65#,16#1E65#,Fs.LL),
         (16#1E66#,16#1E66#,Fs.LU),(16#1E67#,16#1E67#,Fs.LL),(16#1E68#,16#1E68#,Fs.LU),
         (16#1E69#,16#1E69#,Fs.LL),(16#1E6A#,16#1E6A#,Fs.LU),(16#1E6B#,16#1E6B#,Fs.LL),
         (16#1E6C#,16#1E6C#,Fs.LU),(16#1E6D#,16#1E6D#,Fs.LL),(16#1E6E#,16#1E6E#,Fs.LU),
         (16#1E6F#,16#1E6F#,Fs.LL),(16#1E70#,16#1E70#,Fs.LU),(16#1E71#,16#1E71#,Fs.LL),
         (16#1E72#,16#1E72#,Fs.LU),(16#1E73#,16#1E73#,Fs.LL),(16#1E74#,16#1E74#,Fs.LU),
         (16#1E75#,16#1E75#,Fs.LL),(16#1E76#,16#1E76#,Fs.LU),(16#1E77#,16#1E77#,Fs.LL),
         (16#1E78#,16#1E78#,Fs.LU),(16#1E79#,16#1E79#,Fs.LL),(16#1E7A#,16#1E7A#,Fs.LU),
         (16#1E7B#,16#1E7B#,Fs.LL),(16#1E7C#,16#1E7C#,Fs.LU),(16#1E7D#,16#1E7D#,Fs.LL),
         (16#1E7E#,16#1E7E#,Fs.LU),(16#1E7F#,16#1E7F#,Fs.LL),(16#1E80#,16#1E80#,Fs.LU),
         (16#1E81#,16#1E81#,Fs.LL),(16#1E82#,16#1E82#,Fs.LU),(16#1E83#,16#1E83#,Fs.LL),
         (16#1E84#,16#1E84#,Fs.LU),(16#1E85#,16#1E85#,Fs.LL),(16#1E86#,16#1E86#,Fs.LU),
         (16#1E87#,16#1E87#,Fs.LL),(16#1E88#,16#1E88#,Fs.LU),(16#1E89#,16#1E89#,Fs.LL),
         (16#1E8A#,16#1E8A#,Fs.LU),(16#1E8B#,16#1E8B#,Fs.LL),(16#1E8C#,16#1E8C#,Fs.LU),
         (16#1E8D#,16#1E8D#,Fs.LL),(16#1E8E#,16#1E8E#,Fs.LU),(16#1E8F#,16#1E8F#,Fs.LL),
         (16#1E90#,16#1E90#,Fs.LU),(16#1E91#,16#1E91#,Fs.LL),(16#1E92#,16#1E92#,Fs.LU),
         (16#1E93#,16#1E93#,Fs.LL),(16#1E94#,16#1E94#,Fs.LU),(16#1E95#,16#1E9B#,Fs.LL),
         (16#1EA0#,16#1EA0#,Fs.LU),(16#1EA1#,16#1EA1#,Fs.LL),(16#1EA2#,16#1EA2#,Fs.LU),
         (16#1EA3#,16#1EA3#,Fs.LL),(16#1EA4#,16#1EA4#,Fs.LU),(16#1EA5#,16#1EA5#,Fs.LL),
         (16#1EA6#,16#1EA6#,Fs.LU),(16#1EA7#,16#1EA7#,Fs.LL),(16#1EA8#,16#1EA8#,Fs.LU),
         (16#1EA9#,16#1EA9#,Fs.LL),(16#1EAA#,16#1EAA#,Fs.LU),(16#1EAB#,16#1EAB#,Fs.LL),
         (16#1EAC#,16#1EAC#,Fs.LU),(16#1EAD#,16#1EAD#,Fs.LL),(16#1EAE#,16#1EAE#,Fs.LU),
         (16#1EAF#,16#1EAF#,Fs.LL),(16#1EB0#,16#1EB0#,Fs.LU),(16#1EB1#,16#1EB1#,Fs.LL),
         (16#1EB2#,16#1EB2#,Fs.LU),(16#1EB3#,16#1EB3#,Fs.LL),(16#1EB4#,16#1EB4#,Fs.LU),
         (16#1EB5#,16#1EB5#,Fs.LL),(16#1EB6#,16#1EB6#,Fs.LU),(16#1EB7#,16#1EB7#,Fs.LL),
         (16#1EB8#,16#1EB8#,Fs.LU),(16#1EB9#,16#1EB9#,Fs.LL),(16#1EBA#,16#1EBA#,Fs.LU),
         (16#1EBB#,16#1EBB#,Fs.LL),(16#1EBC#,16#1EBC#,Fs.LU),(16#1EBD#,16#1EBD#,Fs.LL),
         (16#1EBE#,16#1EBE#,Fs.LU),(16#1EBF#,16#1EBF#,Fs.LL),(16#1EC0#,16#1EC0#,Fs.LU),
         (16#1EC1#,16#1EC1#,Fs.LL),(16#1EC2#,16#1EC2#,Fs.LU),(16#1EC3#,16#1EC3#,Fs.LL),
         (16#1EC4#,16#1EC4#,Fs.LU),(16#1EC5#,16#1EC5#,Fs.LL),(16#1EC6#,16#1EC6#,Fs.LU),
         (16#1EC7#,16#1EC7#,Fs.LL),(16#1EC8#,16#1EC8#,Fs.LU),(16#1EC9#,16#1EC9#,Fs.LL),
         (16#1ECA#,16#1ECA#,Fs.LU),(16#1ECB#,16#1ECB#,Fs.LL),(16#1ECC#,16#1ECC#,Fs.LU),
         (16#1ECD#,16#1ECD#,Fs.LL),(16#1ECE#,16#1ECE#,Fs.LU),(16#1ECF#,16#1ECF#,Fs.LL),
         (16#1ED0#,16#1ED0#,Fs.LU),(16#1ED1#,16#1ED1#,Fs.LL),(16#1ED2#,16#1ED2#,Fs.LU),
         (16#1ED3#,16#1ED3#,Fs.LL),(16#1ED4#,16#1ED4#,Fs.LU),(16#1ED5#,16#1ED5#,Fs.LL),
         (16#1ED6#,16#1ED6#,Fs.LU),(16#1ED7#,16#1ED7#,Fs.LL),(16#1ED8#,16#1ED8#,Fs.LU),
         (16#1ED9#,16#1ED9#,Fs.LL),(16#1EDA#,16#1EDA#,Fs.LU),(16#1EDB#,16#1EDB#,Fs.LL),
         (16#1EDC#,16#1EDC#,Fs.LU),(16#1EDD#,16#1EDD#,Fs.LL),(16#1EDE#,16#1EDE#,Fs.LU),
         (16#1EDF#,16#1EDF#,Fs.LL),(16#1EE0#,16#1EE0#,Fs.LU),(16#1EE1#,16#1EE1#,Fs.LL),
         (16#1EE2#,16#1EE2#,Fs.LU),(16#1EE3#,16#1EE3#,Fs.LL),(16#1EE4#,16#1EE4#,Fs.LU),
         (16#1EE5#,16#1EE5#,Fs.LL),(16#1EE6#,16#1EE6#,Fs.LU),(16#1EE7#,16#1EE7#,Fs.LL),
         (16#1EE8#,16#1EE8#,Fs.LU),(16#1EE9#,16#1EE9#,Fs.LL),(16#1EEA#,16#1EEA#,Fs.LU),
         (16#1EEB#,16#1EEB#,Fs.LL),(16#1EEC#,16#1EEC#,Fs.LU),(16#1EED#,16#1EED#,Fs.LL),
         (16#1EEE#,16#1EEE#,Fs.LU),(16#1EEF#,16#1EEF#,Fs.LL),(16#1EF0#,16#1EF0#,Fs.LU),
         (16#1EF1#,16#1EF1#,Fs.LL),(16#1EF2#,16#1EF2#,Fs.LU),(16#1EF3#,16#1EF3#,Fs.LL),
         (16#1EF4#,16#1EF4#,Fs.LU),(16#1EF5#,16#1EF5#,Fs.LL),(16#1EF6#,16#1EF6#,Fs.LU),
         (16#1EF7#,16#1EF7#,Fs.LL),(16#1EF8#,16#1EF8#,Fs.LU),(16#1EF9#,16#1EF9#,Fs.LL),
         (16#1F00#,16#1F07#,Fs.LL),(16#1F08#,16#1F0F#,Fs.LU),(16#1F10#,16#1F15#,Fs.LL),
         (16#1F18#,16#1F1D#,Fs.LU),(16#1F20#,16#1F27#,Fs.LL),(16#1F28#,16#1F2F#,Fs.LU),
         (16#1F30#,16#1F37#,Fs.LL),(16#1F38#,16#1F3F#,Fs.LU),(16#1F40#,16#1F45#,Fs.LL),
         (16#1F48#,16#1F4D#,Fs.LU),(16#1F50#,16#1F57#,Fs.LL),(16#1F59#,16#1F59#,Fs.LU),
         (16#1F5B#,16#1F5B#,Fs.LU),(16#1F5D#,16#1F5D#,Fs.LU),(16#1F5F#,16#1F5F#,Fs.LU),
         (16#1F60#,16#1F67#,Fs.LL),(16#1F68#,16#1F6F#,Fs.LU),(16#1F70#,16#1F7D#,Fs.LL),
         (16#1F80#,16#1F87#,Fs.LL),(16#1F88#,16#1F8F#,Fs.LT),(16#1F90#,16#1F97#,Fs.LL),
         (16#1F98#,16#1F9F#,Fs.LT),(16#1FA0#,16#1FA7#,Fs.LL),(16#1FA8#,16#1FAF#,Fs.LT),
         (16#1FB0#,16#1FB4#,Fs.LL),(16#1FB6#,16#1FB7#,Fs.LL),(16#1FB8#,16#1FBB#,Fs.LU),
         (16#1FBC#,16#1FBC#,Fs.LT),(16#1FBD#,16#1FBD#,Fs.SK),(16#1FBE#,16#1FBE#,Fs.LL),
         (16#1FBF#,16#1FC1#,Fs.SK),(16#1FC2#,16#1FC4#,Fs.LL),(16#1FC6#,16#1FC7#,Fs.LL),
         (16#1FC8#,16#1FCB#,Fs.LU),(16#1FCC#,16#1FCC#,Fs.LT),(16#1FCD#,16#1FCF#,Fs.SK),
         (16#1FD0#,16#1FD3#,Fs.LL),(16#1FD6#,16#1FD7#,Fs.LL),(16#1FD8#,16#1FDB#,Fs.LU),
         (16#1FDD#,16#1FDF#,Fs.SK),(16#1FE0#,16#1FE7#,Fs.LL),(16#1FE8#,16#1FEC#,Fs.LU),
         (16#1FED#,16#1FEF#,Fs.SK),(16#1FF2#,16#1FF4#,Fs.LL),(16#1FF6#,16#1FF7#,Fs.LL),
         (16#1FF8#,16#1FFB#,Fs.LU),(16#1FFC#,16#1FFC#,Fs.LT),(16#1FFD#,16#1FFE#,Fs.SK),
         (16#2000#,16#200A#,Fs.ZS),(16#200B#,16#200F#,Fs.CF),(16#2010#,16#2015#,Fs.PD),
         (16#2016#,16#2017#,Fs.PO),(16#2018#,16#2018#,Fs.PI),(16#2019#,16#2019#,Fs.PF),
         (16#201A#,16#201A#,Fs.PS),(16#201B#,16#201C#,Fs.PI),(16#201D#,16#201D#,Fs.PF),
         (16#201E#,16#201E#,Fs.PS),(16#201F#,16#201F#,Fs.PI),(16#2020#,16#2027#,Fs.PO),
         (16#2028#,16#2028#,Fs.ZL),(16#2029#,16#2029#,Fs.ZP),(16#202A#,16#202E#,Fs.CF),
         (16#202F#,16#202F#,Fs.ZS),(16#2030#,16#2038#,Fs.PO),(16#2039#,16#2039#,Fs.PI),
         (16#203A#,16#203A#,Fs.PF),(16#203B#,16#203E#,Fs.PO),(16#203F#,16#2040#,Fs.PC),
         (16#2041#,16#2043#,Fs.PO),(16#2044#,16#2044#,Fs.SM),(16#2045#,16#2045#,Fs.PS),
         (16#2046#,16#2046#,Fs.PE),(16#2047#,16#2051#,Fs.PO),(16#2052#,16#2052#,Fs.SM),
         (16#2053#,16#2053#,Fs.PO),(16#2054#,16#2054#,Fs.PC),(16#2055#,16#205E#,Fs.PO),
         (16#205F#,16#205F#,Fs.ZS),(16#2060#,16#2063#,Fs.CF),(16#206A#,16#206F#,Fs.CF),
         (16#2070#,16#2070#,Fs.NO),(16#2071#,16#2071#,Fs.LL),(16#2074#,16#2079#,Fs.NO),
         (16#207A#,16#207C#,Fs.SM),(16#207D#,16#207D#,Fs.PS),(16#207E#,16#207E#,Fs.PE),
         (16#207F#,16#207F#,Fs.LL),(16#2080#,16#2089#,Fs.NO),(16#208A#,16#208C#,Fs.SM),
         (16#208D#,16#208D#,Fs.PS),(16#208E#,16#208E#,Fs.PE),(16#2090#,16#2094#,Fs.LM),
         (16#20A0#,16#20B5#,Fs.SC),(16#20D0#,16#20DC#,Fs.MN),(16#20DD#,16#20E0#,Fs.ME),
         (16#20E1#,16#20E1#,Fs.MN),(16#20E2#,16#20E4#,Fs.ME),(16#20E5#,16#20EF#,Fs.MN),
         (16#2100#,16#2101#,Fs.SO),(16#2102#,16#2102#,Fs.LU),(16#2103#,16#2106#,Fs.SO),
         (16#2107#,16#2107#,Fs.LU),(16#2108#,16#2109#,Fs.SO),(16#210A#,16#210A#,Fs.LL),
         (16#210B#,16#210D#,Fs.LU),(16#210E#,16#210F#,Fs.LL),(16#2110#,16#2112#,Fs.LU),
         (16#2113#,16#2113#,Fs.LL),(16#2114#,16#2114#,Fs.SO),(16#2115#,16#2115#,Fs.LU),
         (16#2116#,16#2118#,Fs.SO),(16#2119#,16#211D#,Fs.LU),(16#211E#,16#2123#,Fs.SO),
         (16#2124#,16#2124#,Fs.LU),(16#2125#,16#2125#,Fs.SO),(16#2126#,16#2126#,Fs.LU),
         (16#2127#,16#2127#,Fs.SO),(16#2128#,16#2128#,Fs.LU),(16#2129#,16#2129#,Fs.SO),
         (16#212A#,16#212D#,Fs.LU),(16#212E#,16#212E#,Fs.SO),(16#212F#,16#212F#,Fs.LL),
         (16#2130#,16#2133#,Fs.LU),(16#2134#,16#2134#,Fs.LL),(16#2135#,16#2138#,Fs.LO),
         (16#2139#,16#2139#,Fs.LL),(16#213A#,16#213B#,Fs.SO),(16#213C#,16#213D#,Fs.LL),
         (16#213E#,16#213F#,Fs.LU),(16#2140#,16#2144#,Fs.SM),(16#2145#,16#2145#,Fs.LU),
         (16#2146#,16#2149#,Fs.LL),(16#214A#,16#214A#,Fs.SO),(16#214B#,16#214B#,Fs.SM),
         (16#214C#,16#214D#,Fs.SO),(16#214E#,16#214E#,Fs.LL),(16#2153#,16#215F#,Fs.NO),
         (16#2160#,16#2182#,Fs.NL),(16#2183#,16#2183#,Fs.LU),(16#2184#,16#2184#,Fs.LL),
         (16#2190#,16#2194#,Fs.SM),(16#2195#,16#2199#,Fs.SO),(16#219A#,16#219B#,Fs.SM),
         (16#219C#,16#219F#,Fs.SO),(16#21A0#,16#21A0#,Fs.SM),(16#21A1#,16#21A2#,Fs.SO),
         (16#21A3#,16#21A3#,Fs.SM),(16#21A4#,16#21A5#,Fs.SO),(16#21A6#,16#21A6#,Fs.SM),
         (16#21A7#,16#21AD#,Fs.SO),(16#21AE#,16#21AE#,Fs.SM),(16#21AF#,16#21CD#,Fs.SO),
         (16#21CE#,16#21CF#,Fs.SM),(16#21D0#,16#21D1#,Fs.SO),(16#21D2#,16#21D2#,Fs.SM),
         (16#21D3#,16#21D3#,Fs.SO),(16#21D4#,16#21D4#,Fs.SM),(16#21D5#,16#21F3#,Fs.SO),
         (16#21F4#,16#22FF#,Fs.SM),(16#2300#,16#2307#,Fs.SO),(16#2308#,16#230B#,Fs.SM),
         (16#230C#,16#231F#,Fs.SO),(16#2320#,16#2321#,Fs.SM),(16#2322#,16#2328#,Fs.SO),
         (16#2329#,16#2329#,Fs.PS),(16#232A#,16#232A#,Fs.PE),(16#232B#,16#237B#,Fs.SO),
         (16#237C#,16#237C#,Fs.SM),(16#237D#,16#239A#,Fs.SO),(16#239B#,16#23B3#,Fs.SM),
         (16#23B4#,16#23DB#,Fs.SO),(16#23DC#,16#23E1#,Fs.SM),(16#23E2#,16#23E7#,Fs.SO),
         (16#2400#,16#2426#,Fs.SO),(16#2440#,16#244A#,Fs.SO),(16#2460#,16#249B#,Fs.NO),
         (16#249C#,16#24E9#,Fs.SO),(16#24EA#,16#24FF#,Fs.NO),(16#2500#,16#25B6#,Fs.SO),
         (16#25B7#,16#25B7#,Fs.SM),(16#25B8#,16#25C0#,Fs.SO),(16#25C1#,16#25C1#,Fs.SM),
         (16#25C2#,16#25F7#,Fs.SO),(16#25F8#,16#25FF#,Fs.SM),(16#2600#,16#266E#,Fs.SO),
         (16#266F#,16#266F#,Fs.SM),(16#2670#,16#269C#,Fs.SO),(16#26A0#,16#26B2#,Fs.SO),
         (16#2701#,16#2704#,Fs.SO),(16#2706#,16#2709#,Fs.SO),(16#270C#,16#2727#,Fs.SO),
         (16#2729#,16#274B#,Fs.SO),(16#274D#,16#274D#,Fs.SO),(16#274F#,16#2752#,Fs.SO),
         (16#2756#,16#2756#,Fs.SO),(16#2758#,16#275E#,Fs.SO),(16#2761#,16#2767#,Fs.SO),
         (16#2768#,16#2768#,Fs.PS),(16#2769#,16#2769#,Fs.PE),(16#276A#,16#276A#,Fs.PS),
         (16#276B#,16#276B#,Fs.PE),(16#276C#,16#276C#,Fs.PS),(16#276D#,16#276D#,Fs.PE),
         (16#276E#,16#276E#,Fs.PS),(16#276F#,16#276F#,Fs.PE),(16#2770#,16#2770#,Fs.PS),
         (16#2771#,16#2771#,Fs.PE),(16#2772#,16#2772#,Fs.PS),(16#2773#,16#2773#,Fs.PE),
         (16#2774#,16#2774#,Fs.PS),(16#2775#,16#2775#,Fs.PE),(16#2776#,16#2793#,Fs.NO),
         (16#2794#,16#2794#,Fs.SO),(16#2798#,16#27AF#,Fs.SO),(16#27B1#,16#27BE#,Fs.SO),
         (16#27C0#,16#27C4#,Fs.SM),(16#27C5#,16#27C5#,Fs.PS),(16#27C6#,16#27C6#,Fs.PE),
         (16#27C7#,16#27CA#,Fs.SM),(16#27D0#,16#27E5#,Fs.SM),(16#27E6#,16#27E6#,Fs.PS),
         (16#27E7#,16#27E7#,Fs.PE),(16#27E8#,16#27E8#,Fs.PS),(16#27E9#,16#27E9#,Fs.PE),
         (16#27EA#,16#27EA#,Fs.PS),(16#27EB#,16#27EB#,Fs.PE),(16#27F0#,16#27FF#,Fs.SM),
         (16#2800#,16#28FF#,Fs.SO),(16#2900#,16#2982#,Fs.SM),(16#2983#,16#2983#,Fs.PS),
         (16#2984#,16#2984#,Fs.PE),(16#2985#,16#2985#,Fs.PS),(16#2986#,16#2986#,Fs.PE),
         (16#2987#,16#2987#,Fs.PS),(16#2988#,16#2988#,Fs.PE),(16#2989#,16#2989#,Fs.PS),
         (16#298A#,16#298A#,Fs.PE),(16#298B#,16#298B#,Fs.PS),(16#298C#,16#298C#,Fs.PE),
         (16#298D#,16#298D#,Fs.PS),(16#298E#,16#298E#,Fs.PE),(16#298F#,16#298F#,Fs.PS),
         (16#2990#,16#2990#,Fs.PE),(16#2991#,16#2991#,Fs.PS),(16#2992#,16#2992#,Fs.PE),
         (16#2993#,16#2993#,Fs.PS),(16#2994#,16#2994#,Fs.PE),(16#2995#,16#2995#,Fs.PS),
         (16#2996#,16#2996#,Fs.PE),(16#2997#,16#2997#,Fs.PS),(16#2998#,16#2998#,Fs.PE),
         (16#2999#,16#29D7#,Fs.SM),(16#29D8#,16#29D8#,Fs.PS),(16#29D9#,16#29D9#,Fs.PE),
         (16#29DA#,16#29DA#,Fs.PS),(16#29DB#,16#29DB#,Fs.PE),(16#29DC#,16#29FB#,Fs.SM),
         (16#29FC#,16#29FC#,Fs.PS),(16#29FD#,16#29FD#,Fs.PE),(16#29FE#,16#2AFF#,Fs.SM),
         (16#2B00#,16#2B1A#,Fs.SO),(16#2B20#,16#2B23#,Fs.SO),(16#2C00#,16#2C2E#,Fs.LU),
         (16#2C30#,16#2C5E#,Fs.LL),(16#2C60#,16#2C60#,Fs.LU),(16#2C61#,16#2C61#,Fs.LL),
         (16#2C62#,16#2C64#,Fs.LU),(16#2C65#,16#2C66#,Fs.LL),(16#2C67#,16#2C67#,Fs.LU),
         (16#2C68#,16#2C68#,Fs.LL),(16#2C69#,16#2C69#,Fs.LU),(16#2C6A#,16#2C6A#,Fs.LL),
         (16#2C6B#,16#2C6B#,Fs.LU),(16#2C6C#,16#2C6C#,Fs.LL),(16#2C74#,16#2C74#,Fs.LL),
         (16#2C75#,16#2C75#,Fs.LU),(16#2C76#,16#2C77#,Fs.LL),(16#2C80#,16#2C80#,Fs.LU),
         (16#2C81#,16#2C81#,Fs.LL),(16#2C82#,16#2C82#,Fs.LU),(16#2C83#,16#2C83#,Fs.LL),
         (16#2C84#,16#2C84#,Fs.LU),(16#2C85#,16#2C85#,Fs.LL),(16#2C86#,16#2C86#,Fs.LU),
         (16#2C87#,16#2C87#,Fs.LL),(16#2C88#,16#2C88#,Fs.LU),(16#2C89#,16#2C89#,Fs.LL),
         (16#2C8A#,16#2C8A#,Fs.LU),(16#2C8B#,16#2C8B#,Fs.LL),(16#2C8C#,16#2C8C#,Fs.LU),
         (16#2C8D#,16#2C8D#,Fs.LL),(16#2C8E#,16#2C8E#,Fs.LU),(16#2C8F#,16#2C8F#,Fs.LL),
         (16#2C90#,16#2C90#,Fs.LU),(16#2C91#,16#2C91#,Fs.LL),(16#2C92#,16#2C92#,Fs.LU),
         (16#2C93#,16#2C93#,Fs.LL),(16#2C94#,16#2C94#,Fs.LU),(16#2C95#,16#2C95#,Fs.LL),
         (16#2C96#,16#2C96#,Fs.LU),(16#2C97#,16#2C97#,Fs.LL),(16#2C98#,16#2C98#,Fs.LU),
         (16#2C99#,16#2C99#,Fs.LL),(16#2C9A#,16#2C9A#,Fs.LU),(16#2C9B#,16#2C9B#,Fs.LL),
         (16#2C9C#,16#2C9C#,Fs.LU),(16#2C9D#,16#2C9D#,Fs.LL),(16#2C9E#,16#2C9E#,Fs.LU),
         (16#2C9F#,16#2C9F#,Fs.LL),(16#2CA0#,16#2CA0#,Fs.LU),(16#2CA1#,16#2CA1#,Fs.LL),
         (16#2CA2#,16#2CA2#,Fs.LU),(16#2CA3#,16#2CA3#,Fs.LL),(16#2CA4#,16#2CA4#,Fs.LU),
         (16#2CA5#,16#2CA5#,Fs.LL),(16#2CA6#,16#2CA6#,Fs.LU),(16#2CA7#,16#2CA7#,Fs.LL),
         (16#2CA8#,16#2CA8#,Fs.LU),(16#2CA9#,16#2CA9#,Fs.LL),(16#2CAA#,16#2CAA#,Fs.LU),
         (16#2CAB#,16#2CAB#,Fs.LL),(16#2CAC#,16#2CAC#,Fs.LU),(16#2CAD#,16#2CAD#,Fs.LL),
         (16#2CAE#,16#2CAE#,Fs.LU),(16#2CAF#,16#2CAF#,Fs.LL),(16#2CB0#,16#2CB0#,Fs.LU),
         (16#2CB1#,16#2CB1#,Fs.LL),(16#2CB2#,16#2CB2#,Fs.LU),(16#2CB3#,16#2CB3#,Fs.LL),
         (16#2CB4#,16#2CB4#,Fs.LU),(16#2CB5#,16#2CB5#,Fs.LL),(16#2CB6#,16#2CB6#,Fs.LU),
         (16#2CB7#,16#2CB7#,Fs.LL),(16#2CB8#,16#2CB8#,Fs.LU),(16#2CB9#,16#2CB9#,Fs.LL),
         (16#2CBA#,16#2CBA#,Fs.LU),(16#2CBB#,16#2CBB#,Fs.LL),(16#2CBC#,16#2CBC#,Fs.LU),
         (16#2CBD#,16#2CBD#,Fs.LL),(16#2CBE#,16#2CBE#,Fs.LU),(16#2CBF#,16#2CBF#,Fs.LL),
         (16#2CC0#,16#2CC0#,Fs.LU),(16#2CC1#,16#2CC1#,Fs.LL),(16#2CC2#,16#2CC2#,Fs.LU),
         (16#2CC3#,16#2CC3#,Fs.LL),(16#2CC4#,16#2CC4#,Fs.LU),(16#2CC5#,16#2CC5#,Fs.LL),
         (16#2CC6#,16#2CC6#,Fs.LU),(16#2CC7#,16#2CC7#,Fs.LL),(16#2CC8#,16#2CC8#,Fs.LU),
         (16#2CC9#,16#2CC9#,Fs.LL),(16#2CCA#,16#2CCA#,Fs.LU),(16#2CCB#,16#2CCB#,Fs.LL),
         (16#2CCC#,16#2CCC#,Fs.LU),(16#2CCD#,16#2CCD#,Fs.LL),(16#2CCE#,16#2CCE#,Fs.LU),
         (16#2CCF#,16#2CCF#,Fs.LL),(16#2CD0#,16#2CD0#,Fs.LU),(16#2CD1#,16#2CD1#,Fs.LL),
         (16#2CD2#,16#2CD2#,Fs.LU),(16#2CD3#,16#2CD3#,Fs.LL),(16#2CD4#,16#2CD4#,Fs.LU),
         (16#2CD5#,16#2CD5#,Fs.LL),(16#2CD6#,16#2CD6#,Fs.LU),(16#2CD7#,16#2CD7#,Fs.LL),
         (16#2CD8#,16#2CD8#,Fs.LU),(16#2CD9#,16#2CD9#,Fs.LL),(16#2CDA#,16#2CDA#,Fs.LU),
         (16#2CDB#,16#2CDB#,Fs.LL),(16#2CDC#,16#2CDC#,Fs.LU),(16#2CDD#,16#2CDD#,Fs.LL),
         (16#2CDE#,16#2CDE#,Fs.LU),(16#2CDF#,16#2CDF#,Fs.LL),(16#2CE0#,16#2CE0#,Fs.LU),
         (16#2CE1#,16#2CE1#,Fs.LL),(16#2CE2#,16#2CE2#,Fs.LU),(16#2CE3#,16#2CE4#,Fs.LL),
         (16#2CE5#,16#2CEA#,Fs.SO),(16#2CF9#,16#2CFC#,Fs.PO),(16#2CFD#,16#2CFD#,Fs.NO),
         (16#2CFE#,16#2CFF#,Fs.PO),(16#2D00#,16#2D25#,Fs.LL),(16#2D30#,16#2D65#,Fs.LO),
         (16#2D6F#,16#2D6F#,Fs.LM),(16#2D80#,16#2D96#,Fs.LO),(16#2DA0#,16#2DA6#,Fs.LO),
         (16#2DA8#,16#2DAE#,Fs.LO),(16#2DB0#,16#2DB6#,Fs.LO),(16#2DB8#,16#2DBE#,Fs.LO),
         (16#2DC0#,16#2DC6#,Fs.LO),(16#2DC8#,16#2DCE#,Fs.LO),(16#2DD0#,16#2DD6#,Fs.LO),
         (16#2DD8#,16#2DDE#,Fs.LO),(16#2E00#,16#2E01#,Fs.PO),(16#2E02#,16#2E02#,Fs.PI),
         (16#2E03#,16#2E03#,Fs.PF),(16#2E04#,16#2E04#,Fs.PI),(16#2E05#,16#2E05#,Fs.PF),
         (16#2E06#,16#2E08#,Fs.PO),(16#2E09#,16#2E09#,Fs.PI),(16#2E0A#,16#2E0A#,Fs.PF),
         (16#2E0B#,16#2E0B#,Fs.PO),(16#2E0C#,16#2E0C#,Fs.PI),(16#2E0D#,16#2E0D#,Fs.PF),
         (16#2E0E#,16#2E16#,Fs.PO),(16#2E17#,16#2E17#,Fs.PD),(16#2E1C#,16#2E1C#,Fs.PI),
         (16#2E1D#,16#2E1D#,Fs.PF),(16#2E80#,16#2E99#,Fs.SO),(16#2E9B#,16#2EF3#,Fs.SO),
         (16#2F00#,16#2FD5#,Fs.SO),(16#2FF0#,16#2FFB#,Fs.SO),(16#3000#,16#3000#,Fs.ZS),
         (16#3001#,16#3003#,Fs.PO),(16#3004#,16#3004#,Fs.SO),(16#3005#,16#3005#,Fs.LM),
         (16#3006#,16#3006#,Fs.LO),(16#3007#,16#3007#,Fs.NL),(16#3008#,16#3008#,Fs.PS),
         (16#3009#,16#3009#,Fs.PE),(16#300A#,16#300A#,Fs.PS),(16#300B#,16#300B#,Fs.PE),
         (16#300C#,16#300C#,Fs.PS),(16#300D#,16#300D#,Fs.PE),(16#300E#,16#300E#,Fs.PS),
         (16#300F#,16#300F#,Fs.PE),(16#3010#,16#3010#,Fs.PS),(16#3011#,16#3011#,Fs.PE),
         (16#3012#,16#3013#,Fs.SO),(16#3014#,16#3014#,Fs.PS),(16#3015#,16#3015#,Fs.PE),
         (16#3016#,16#3016#,Fs.PS),(16#3017#,16#3017#,Fs.PE),(16#3018#,16#3018#,Fs.PS),
         (16#3019#,16#3019#,Fs.PE),(16#301A#,16#301A#,Fs.PS),(16#301B#,16#301B#,Fs.PE),
         (16#301C#,16#301C#,Fs.PD),(16#301D#,16#301D#,Fs.PS),(16#301E#,16#301F#,Fs.PE),
         (16#3020#,16#3020#,Fs.SO),(16#3021#,16#3029#,Fs.NL),(16#302A#,16#302F#,Fs.MN),
         (16#3030#,16#3030#,Fs.PD),(16#3031#,16#3035#,Fs.LM),(16#3036#,16#3037#,Fs.SO),
         (16#3038#,16#303A#,Fs.NL),(16#303B#,16#303B#,Fs.LM),(16#303C#,16#303C#,Fs.LO),
         (16#303D#,16#303D#,Fs.PO),(16#303E#,16#303F#,Fs.SO),(16#3041#,16#3096#,Fs.LO),
         (16#3099#,16#309A#,Fs.MN),(16#309B#,16#309C#,Fs.SK),(16#309D#,16#309E#,Fs.LM),
         (16#309F#,16#309F#,Fs.LO),(16#30A0#,16#30A0#,Fs.PD),(16#30A1#,16#30FA#,Fs.LO),
         (16#30FB#,16#30FB#,Fs.PO),(16#30FC#,16#30FE#,Fs.LM),(16#30FF#,16#30FF#,Fs.LO),
         (16#3105#,16#312C#,Fs.LO),(16#3131#,16#318E#,Fs.LO),(16#3190#,16#3191#,Fs.SO),
         (16#3192#,16#3195#,Fs.NO),(16#3196#,16#319F#,Fs.SO),(16#31A0#,16#31B7#,Fs.LO),
         (16#31C0#,16#31CF#,Fs.SO),(16#31F0#,16#31FF#,Fs.LO),(16#3200#,16#321E#,Fs.SO),
         (16#3220#,16#3229#,Fs.NO),(16#322A#,16#3243#,Fs.SO),(16#3250#,16#3250#,Fs.SO),
         (16#3251#,16#325F#,Fs.NO),(16#3260#,16#327F#,Fs.SO),(16#3280#,16#3289#,Fs.NO),
         (16#328A#,16#32B0#,Fs.SO),(16#32B1#,16#32BF#,Fs.NO),(16#32C0#,16#32FE#,Fs.SO),
         (16#3300#,16#33FF#,Fs.SO),(16#3400#,16#3400#,Fs.LO),(16#4DB5#,16#4DB5#,Fs.LO),
         (16#4DC0#,16#4DFF#,Fs.SO),(16#4E00#,16#4E00#,Fs.LO),(16#9FBB#,16#9FBB#,Fs.LO),
         (16#A000#,16#A014#,Fs.LO),(16#A015#,16#A015#,Fs.LM),(16#A016#,16#A48C#,Fs.LO),
         (16#A490#,16#A4C6#,Fs.SO),(16#A700#,16#A716#,Fs.SK),(16#A717#,16#A71A#,Fs.LM),
         (16#A720#,16#A721#,Fs.SK),(16#A800#,16#A801#,Fs.LO),(16#A802#,16#A802#,Fs.MC),
         (16#A803#,16#A805#,Fs.LO),(16#A806#,16#A806#,Fs.MN),(16#A807#,16#A80A#,Fs.LO),
         (16#A80B#,16#A80B#,Fs.MN),(16#A80C#,16#A822#,Fs.LO),(16#A823#,16#A824#,Fs.MC),
         (16#A825#,16#A826#,Fs.MN),(16#A827#,16#A827#,Fs.MC),(16#A828#,16#A82B#,Fs.SO),
         (16#A840#,16#A873#,Fs.LO),(16#A874#,16#A877#,Fs.PO),(16#AC00#,16#AC00#,Fs.LO),
         (16#D7A3#,16#D7A3#,Fs.LO),(16#D800#,16#D800#,Fs.CS),(16#DB7F#,16#DB80#,Fs.CS),
         (16#DBFF#,16#DC00#,Fs.CS),(16#DFFF#,16#DFFF#,Fs.CS),(16#E000#,16#E000#,Fs.CO),
         (16#F8FF#,16#F8FF#,Fs.CO),(16#F900#,16#FA2D#,Fs.LO),(16#FA30#,16#FA6A#,Fs.LO),
         (16#FA70#,16#FAD9#,Fs.LO),(16#FB00#,16#FB06#,Fs.LL),(16#FB13#,16#FB17#,Fs.LL),
         (16#FB1D#,16#FB1D#,Fs.LO),(16#FB1E#,16#FB1E#,Fs.MN),(16#FB1F#,16#FB28#,Fs.LO),
         (16#FB29#,16#FB29#,Fs.SM),(16#FB2A#,16#FB36#,Fs.LO),(16#FB38#,16#FB3C#,Fs.LO),
         (16#FB3E#,16#FB3E#,Fs.LO),(16#FB40#,16#FB41#,Fs.LO),(16#FB43#,16#FB44#,Fs.LO),
         (16#FB46#,16#FBB1#,Fs.LO),(16#FBD3#,16#FD3D#,Fs.LO),(16#FD3E#,16#FD3E#,Fs.PS),
         (16#FD3F#,16#FD3F#,Fs.PE),(16#FD50#,16#FD8F#,Fs.LO),(16#FD92#,16#FDC7#,Fs.LO),
         (16#FDF0#,16#FDFB#,Fs.LO),(16#FDFC#,16#FDFC#,Fs.SC),(16#FDFD#,16#FDFD#,Fs.SO),
         (16#FE00#,16#FE0F#,Fs.MN),(16#FE10#,16#FE16#,Fs.PO),(16#FE17#,16#FE17#,Fs.PS),
         (16#FE18#,16#FE18#,Fs.PE),(16#FE19#,16#FE19#,Fs.PO),(16#FE20#,16#FE23#,Fs.MN),
         (16#FE30#,16#FE30#,Fs.PO),(16#FE31#,16#FE32#,Fs.PD),(16#FE33#,16#FE34#,Fs.PC),
         (16#FE35#,16#FE35#,Fs.PS),(16#FE36#,16#FE36#,Fs.PE),(16#FE37#,16#FE37#,Fs.PS),
         (16#FE38#,16#FE38#,Fs.PE),(16#FE39#,16#FE39#,Fs.PS),(16#FE3A#,16#FE3A#,Fs.PE),
         (16#FE3B#,16#FE3B#,Fs.PS),(16#FE3C#,16#FE3C#,Fs.PE),(16#FE3D#,16#FE3D#,Fs.PS),
         (16#FE3E#,16#FE3E#,Fs.PE),(16#FE3F#,16#FE3F#,Fs.PS),(16#FE40#,16#FE40#,Fs.PE),
         (16#FE41#,16#FE41#,Fs.PS),(16#FE42#,16#FE42#,Fs.PE),(16#FE43#,16#FE43#,Fs.PS),
         (16#FE44#,16#FE44#,Fs.PE),(16#FE45#,16#FE46#,Fs.PO),(16#FE47#,16#FE47#,Fs.PS),
         (16#FE48#,16#FE48#,Fs.PE),(16#FE49#,16#FE4C#,Fs.PO),(16#FE4D#,16#FE4F#,Fs.PC),
         (16#FE50#,16#FE52#,Fs.PO),(16#FE54#,16#FE57#,Fs.PO),(16#FE58#,16#FE58#,Fs.PD),
         (16#FE59#,16#FE59#,Fs.PS),(16#FE5A#,16#FE5A#,Fs.PE),(16#FE5B#,16#FE5B#,Fs.PS),
         (16#FE5C#,16#FE5C#,Fs.PE),(16#FE5D#,16#FE5D#,Fs.PS),(16#FE5E#,16#FE5E#,Fs.PE),
         (16#FE5F#,16#FE61#,Fs.PO),(16#FE62#,16#FE62#,Fs.SM),(16#FE63#,16#FE63#,Fs.PD),
         (16#FE64#,16#FE66#,Fs.SM),(16#FE68#,16#FE68#,Fs.PO),(16#FE69#,16#FE69#,Fs.SC),
         (16#FE6A#,16#FE6B#,Fs.PO),(16#FE70#,16#FE74#,Fs.LO),(16#FE76#,16#FEFC#,Fs.LO),
         (16#FEFF#,16#FEFF#,Fs.CF),(16#FF01#,16#FF03#,Fs.PO),(16#FF04#,16#FF04#,Fs.SC),
         (16#FF05#,16#FF07#,Fs.PO),(16#FF08#,16#FF08#,Fs.PS),(16#FF09#,16#FF09#,Fs.PE),
         (16#FF0A#,16#FF0A#,Fs.PO),(16#FF0B#,16#FF0B#,Fs.SM),(16#FF0C#,16#FF0C#,Fs.PO),
         (16#FF0D#,16#FF0D#,Fs.PD),(16#FF0E#,16#FF0F#,Fs.PO),(16#FF10#,16#FF19#,Fs.ND),
         (16#FF1A#,16#FF1B#,Fs.PO),(16#FF1C#,16#FF1E#,Fs.SM),(16#FF1F#,16#FF20#,Fs.PO),
         (16#FF21#,16#FF3A#,Fs.LU),(16#FF3B#,16#FF3B#,Fs.PS),(16#FF3C#,16#FF3C#,Fs.PO),
         (16#FF3D#,16#FF3D#,Fs.PE),(16#FF3E#,16#FF3E#,Fs.SK),(16#FF3F#,16#FF3F#,Fs.PC),
         (16#FF40#,16#FF40#,Fs.SK),(16#FF41#,16#FF5A#,Fs.LL),(16#FF5B#,16#FF5B#,Fs.PS),
         (16#FF5C#,16#FF5C#,Fs.SM),(16#FF5D#,16#FF5D#,Fs.PE),(16#FF5E#,16#FF5E#,Fs.SM),
         (16#FF5F#,16#FF5F#,Fs.PS),(16#FF60#,16#FF60#,Fs.PE),(16#FF61#,16#FF61#,Fs.PO),
         (16#FF62#,16#FF62#,Fs.PS),(16#FF63#,16#FF63#,Fs.PE),(16#FF64#,16#FF65#,Fs.PO),
         (16#FF66#,16#FF6F#,Fs.LO),(16#FF70#,16#FF70#,Fs.LM),(16#FF71#,16#FF9D#,Fs.LO),
         (16#FF9E#,16#FF9F#,Fs.LM),(16#FFA0#,16#FFBE#,Fs.LO),(16#FFC2#,16#FFC7#,Fs.LO),
         (16#FFCA#,16#FFCF#,Fs.LO),(16#FFD2#,16#FFD7#,Fs.LO),(16#FFDA#,16#FFDC#,Fs.LO),
         (16#FFE0#,16#FFE1#,Fs.SC),(16#FFE2#,16#FFE2#,Fs.SM),(16#FFE3#,16#FFE3#,Fs.SK),
         (16#FFE4#,16#FFE4#,Fs.SO),(16#FFE5#,16#FFE6#,Fs.SC),(16#FFE8#,16#FFE8#,Fs.SO),
         (16#FFE9#,16#FFEC#,Fs.SM),(16#FFED#,16#FFEE#,Fs.SO),(16#FFF9#,16#FFFB#,Fs.CF),
         (16#FFFC#,16#FFFD#,Fs.SO),(16#10000#,16#1000B#,Fs.LO),(16#1000D#,16#10026#,Fs.LO),
         (16#10028#,16#1003A#,Fs.LO),(16#1003C#,16#1003D#,Fs.LO),(16#1003F#,16#1004D#,Fs.LO),
         (16#10050#,16#1005D#,Fs.LO),(16#10080#,16#100FA#,Fs.LO),(16#10100#,16#10101#,Fs.PO),
         (16#10102#,16#10102#,Fs.SO),(16#10107#,16#10133#,Fs.NO),(16#10137#,16#1013F#,Fs.SO),
         (16#10140#,16#10174#,Fs.NL),(16#10175#,16#10178#,Fs.NO),(16#10179#,16#10189#,Fs.SO),
         (16#1018A#,16#1018A#,Fs.NO),(16#10300#,16#1031E#,Fs.LO),(16#10320#,16#10323#,Fs.NO),
         (16#10330#,16#10340#,Fs.LO),(16#10341#,16#10341#,Fs.NL),(16#10342#,16#10349#,Fs.LO),
         (16#1034A#,16#1034A#,Fs.NL),(16#10380#,16#1039D#,Fs.LO),(16#1039F#,16#1039F#,Fs.PO),
         (16#103A0#,16#103C3#,Fs.LO),(16#103C8#,16#103CF#,Fs.LO),(16#103D0#,16#103D0#,Fs.PO),
         (16#103D1#,16#103D5#,Fs.NL),(16#10400#,16#10427#,Fs.LU),(16#10428#,16#1044F#,Fs.LL),
         (16#10450#,16#1049D#,Fs.LO),(16#104A0#,16#104A9#,Fs.ND),(16#10800#,16#10805#,Fs.LO),
         (16#10808#,16#10808#,Fs.LO),(16#1080A#,16#10835#,Fs.LO),(16#10837#,16#10838#,Fs.LO),
         (16#1083C#,16#1083C#,Fs.LO),(16#1083F#,16#1083F#,Fs.LO),(16#10900#,16#10915#,Fs.LO),
         (16#10916#,16#10919#,Fs.NO),(16#1091F#,16#1091F#,Fs.PO),(16#10A00#,16#10A00#,Fs.LO),
         (16#10A01#,16#10A03#,Fs.MN),(16#10A05#,16#10A06#,Fs.MN),(16#10A0C#,16#10A0F#,Fs.MN),
         (16#10A10#,16#10A13#,Fs.LO),(16#10A15#,16#10A17#,Fs.LO),(16#10A19#,16#10A33#,Fs.LO),
         (16#10A38#,16#10A3A#,Fs.MN),(16#10A3F#,16#10A3F#,Fs.MN),(16#10A40#,16#10A47#,Fs.NO),
         (16#10A50#,16#10A58#,Fs.PO),(16#12000#,16#1236E#,Fs.LO),(16#12400#,16#12462#,Fs.NL),
         (16#12470#,16#12473#,Fs.PO),(16#1D000#,16#1D0F5#,Fs.SO),(16#1D100#,16#1D126#,Fs.SO),
         (16#1D12A#,16#1D164#,Fs.SO),(16#1D165#,16#1D166#,Fs.MC),(16#1D167#,16#1D169#,Fs.MN),
         (16#1D16A#,16#1D16C#,Fs.SO),(16#1D16D#,16#1D172#,Fs.MC),(16#1D173#,16#1D17A#,Fs.CF),
         (16#1D17B#,16#1D182#,Fs.MN),(16#1D183#,16#1D184#,Fs.SO),(16#1D185#,16#1D18B#,Fs.MN),
         (16#1D18C#,16#1D1A9#,Fs.SO),(16#1D1AA#,16#1D1AD#,Fs.MN),(16#1D1AE#,16#1D1DD#,Fs.SO),
         (16#1D200#,16#1D241#,Fs.SO),(16#1D242#,16#1D244#,Fs.MN),(16#1D245#,16#1D245#,Fs.SO),
         (16#1D300#,16#1D356#,Fs.SO),(16#1D360#,16#1D371#,Fs.NO),(16#1D400#,16#1D419#,Fs.LU),
         (16#1D41A#,16#1D433#,Fs.LL),(16#1D434#,16#1D44D#,Fs.LU),(16#1D44E#,16#1D454#,Fs.LL),
         (16#1D456#,16#1D467#,Fs.LL),(16#1D468#,16#1D481#,Fs.LU),(16#1D482#,16#1D49B#,Fs.LL),
         (16#1D49C#,16#1D49C#,Fs.LU),(16#1D49E#,16#1D49F#,Fs.LU),(16#1D4A2#,16#1D4A2#,Fs.LU),
         (16#1D4A5#,16#1D4A6#,Fs.LU),(16#1D4A9#,16#1D4AC#,Fs.LU),(16#1D4AE#,16#1D4B5#,Fs.LU),
         (16#1D4B6#,16#1D4B9#,Fs.LL),(16#1D4BB#,16#1D4BB#,Fs.LL),(16#1D4BD#,16#1D4C3#,Fs.LL),
         (16#1D4C5#,16#1D4CF#,Fs.LL),(16#1D4D0#,16#1D4E9#,Fs.LU),(16#1D4EA#,16#1D503#,Fs.LL),
         (16#1D504#,16#1D505#,Fs.LU),(16#1D507#,16#1D50A#,Fs.LU),(16#1D50D#,16#1D514#,Fs.LU),
         (16#1D516#,16#1D51C#,Fs.LU),(16#1D51E#,16#1D537#,Fs.LL),(16#1D538#,16#1D539#,Fs.LU),
         (16#1D53B#,16#1D53E#,Fs.LU),(16#1D540#,16#1D544#,Fs.LU),(16#1D546#,16#1D546#,Fs.LU),
         (16#1D54A#,16#1D550#,Fs.LU),(16#1D552#,16#1D56B#,Fs.LL),(16#1D56C#,16#1D585#,Fs.LU),
         (16#1D586#,16#1D59F#,Fs.LL),(16#1D5A0#,16#1D5B9#,Fs.LU),(16#1D5BA#,16#1D5D3#,Fs.LL),
         (16#1D5D4#,16#1D5ED#,Fs.LU),(16#1D5EE#,16#1D607#,Fs.LL),(16#1D608#,16#1D621#,Fs.LU),
         (16#1D622#,16#1D63B#,Fs.LL),(16#1D63C#,16#1D655#,Fs.LU),(16#1D656#,16#1D66F#,Fs.LL),
         (16#1D670#,16#1D689#,Fs.LU),(16#1D68A#,16#1D6A5#,Fs.LL),(16#1D6A8#,16#1D6C0#,Fs.LU),
         (16#1D6C1#,16#1D6C1#,Fs.SM),(16#1D6C2#,16#1D6DA#,Fs.LL),(16#1D6DB#,16#1D6DB#,Fs.SM),
         (16#1D6DC#,16#1D6E1#,Fs.LL),(16#1D6E2#,16#1D6FA#,Fs.LU),(16#1D6FB#,16#1D6FB#,Fs.SM),
         (16#1D6FC#,16#1D714#,Fs.LL),(16#1D715#,16#1D715#,Fs.SM),(16#1D716#,16#1D71B#,Fs.LL),
         (16#1D71C#,16#1D734#,Fs.LU),(16#1D735#,16#1D735#,Fs.SM),(16#1D736#,16#1D74E#,Fs.LL),
         (16#1D74F#,16#1D74F#,Fs.SM),(16#1D750#,16#1D755#,Fs.LL),(16#1D756#,16#1D76E#,Fs.LU),
         (16#1D76F#,16#1D76F#,Fs.SM),(16#1D770#,16#1D788#,Fs.LL),(16#1D789#,16#1D789#,Fs.SM),
         (16#1D78A#,16#1D78F#,Fs.LL),(16#1D790#,16#1D7A8#,Fs.LU),(16#1D7A9#,16#1D7A9#,Fs.SM),
         (16#1D7AA#,16#1D7C2#,Fs.LL),(16#1D7C3#,16#1D7C3#,Fs.SM),(16#1D7C4#,16#1D7C9#,Fs.LL),
         (16#1D7CA#,16#1D7CA#,Fs.LU),(16#1D7CB#,16#1D7CB#,Fs.LL),(16#1D7CE#,16#1D7FF#,Fs.ND),
         (16#20000#,16#20000#,Fs.LO),(16#2A6D6#,16#2A6D6#,Fs.LO),(16#2F800#,16#2FA1D#,Fs.LO),
         (16#E0001#,16#E0001#,Fs.CF),(16#E0020#,16#E007F#,Fs.CF),(16#E0100#,16#E01EF#,Fs.MN),
         (16#F0000#,16#F0000#,Fs.CO),(16#FFFFD#,16#FFFFD#,Fs.CO),(16#100000#,16#100000#,Fs.CO),
         (16#10FFFD#,16#10FFFD#,Fs.CO)
        );

      -- Needs to be formally verified:
      function Category (Value : T) return Fs.General_Category is
         From : Range_Index := Category_Mapping'First;
         To   : Range_Index := Category_Mapping'Last;
         This : Range_Index;
         Current : Points_Range;
      begin
         loop
            This := (From + To) / 2;
            Current := Category_Mapping (This);
            if Current.From > Value then
               exit when This = From;
               To := This - 1;
            elsif Current.To < Value then
               exit when This = To;
               From := This + 1;
            else
               return Current.Category;
            end if;
         end loop;
         return Fs.Co;
      end Category;

      -- Verified by: SPARK GPL 2016
      -- Level: None
      -- Elapsed time: 12 seconds
      function Is_Alphanumeric (Value : in T) return Boolean is
      begin
         case Category (Value) is
         when Fs.Letter | Fs.Nd =>
            return True;
         when others =>
            return False;
         end case;
      end Is_Alphanumeric;

      -- Verified by: SPARK GPL 2016
      -- Level: None
      -- Elapsed time: 12 seconds
      function Is_Control (Value : in T) return Boolean is
      begin
         return Category (Value) = Fs.Cc;
      end Is_Control;

      -- Verified by: SPARK GPL 2016
      -- Level: None
      -- Elapsed time: 12 seconds
      function Is_Identifier_Extend (Value : in T) return Boolean is
      begin
         case Category (Value) is
         when Mn | Mc | Nd | Pc | Cf =>
            return True;
         when others =>
            return False;
         end case;
      end Is_Identifier_Extend;

      -- Verified by: SPARK GPL 2016
      -- Level: None
      -- Elapsed time: 12 seconds
      function Is_Identifier_Start (Value : in T) return Boolean is
      begin
         case Category (Value) is
         when Fs.Letter | Fs.Nl =>
            return True;
         when others =>
            return False;
         end case;
      end Is_Identifier_Start;

      -- Verified by: SPARK GPL 2016
      -- Level: None
      -- Elapsed time: 12 seconds
      function Is_ISO_646 (Value : in T) return Boolean is
      begin
         return Value <= 16#7F#;
      end Is_ISO_646;

      -- Verified by: SPARK GPL 2016
      -- Level: None
      -- Elapsed time: 12 seconds
      function Is_Letter (Value : in T) return Boolean is
      begin
         return Category (Value) in Fs.Letter;
      end Is_Letter;

      -- Verified by: SPARK GPL 2016
      -- Level: None
      -- Elapsed time: 12 seconds
      function Is_Lower (Value : in T) return Boolean is
      begin
         return Category (Value) = Ll;
      end Is_Lower;

      -- Verified by: SPARK GPL 2016
      -- Level: None
      -- Elapsed time: 12 seconds
      function Is_Digit (Value : in T) return Boolean is
      begin
         return Category (Value) = Nd;
      end Is_Digit;

      -- Verified by: SPARK GPL 2016
      -- Level: None
      -- Elapsed time: 12 seconds
      function Is_Other_Format (Value : in T) return Boolean is
      begin
         return Category (Value) = Cf;
      end Is_Other_Format;

      -- Verified by: SPARK GPL 2016
      -- Level: None
      -- Elapsed time: 12 seconds
      function Is_Space (Value : in T) return Boolean is
      begin
         return Category (Value) = Zs;
      end Is_Space;

      -- Verified by: SPARK GPL 2016
      -- Level: None
      -- Elapsed time: 12 seconds
      function Is_Subscript_Digit (Value : in T)
                                   return Boolean is
      begin
         return Value in 16#2080#..16#208A#;
      end Is_Subscript_Digit;

      -- Verified by: SPARK GPL 2016
      -- Level: None
      -- Elapsed time: 12 seconds
      function Is_Superscript_Digit (Value : in T) return Boolean is
      begin
         case Value is
         when 16#B2#..16#B3# | 16#B9# | 16#2070#..16#2079# =>
            return True;
         when others =>
            return False;
         end case;
      end Is_Superscript_Digit;

      -- Verified by: SPARK GPL 2016
      -- Level: None
      -- Elapsed time: 12 seconds
      function Is_Title (Value : in T) return Boolean is
      begin
         return Category (Value) = Lt;
      end Is_Title;

      -- Verified by: SPARK GPL 2016
      -- Level: None
      -- Elapsed time: 12 seconds
      function Is_Upper (Value : in T) return Boolean is
      begin
         return Category (Value) = Lu;
      end Is_Upper;

   end UTF8_Code_Point;

   package body UTF8 is

      function Is_Valid_UTF8_Code_Point (Source      : String_T;
                                         Pointer     : Positive) return Boolean
      is
         Last : constant Positive := Positive (Int32_T'Last);
      begin
         if (Source'First <= Pointer and Pointer <= Source'Last) then
            if (Standard.Character'Pos (Source (Pointer)) in 0..16#7F#) then
               return Pointer < Last;
            elsif Pointer < Source'Last then
               if
                 Standard.Character'Pos (Source (Pointer + 0)) in 16#C2#..16#DF# and
                 Standard.Character'Pos (Source (Pointer + 1)) in 16#80#..16#BF#
               then
                  return Pointer < Last - 1;
               elsif Pointer < Source'Last - 1 then
                  if
                    Standard.Character'Pos (Source (Pointer + 0)) = 16#E0# and
                    Standard.Character'Pos (Source (Pointer + 1)) in 16#A0#..16#BF# and
                    Standard.Character'Pos (Source (Pointer + 2)) in 16#80#..16#BF#
                  then
                     return Pointer < Last - 2;
                  elsif
                    Standard.Character'Pos (Source (Pointer + 0)) in 16#E1#..16#EF# and
                    Standard.Character'Pos (Source (Pointer + 1)) in 16#80#..16#BF# and
                    Standard.Character'Pos (Source (Pointer + 2)) in 16#80#..16#BF#
                  then
                     return Pointer < Last - 2;
                  elsif Pointer < Source'Last - 2 then
                     if
                       Standard.Character'Pos (Source (Pointer + 0)) = 16#F0# and
                       Standard.Character'Pos (Source (Pointer + 1)) in 16#90#..16#BF# and
                       Standard.Character'Pos (Source (Pointer + 2)) in 16#80#..16#BF# and
                       Standard.Character'Pos (Source (Pointer + 3)) in 16#80#..16#BF#
                     then
                        return Pointer < Last - 3;
                     elsif
                       Standard.Character'Pos (Source (Pointer + 0)) in 16#F1#..16#F3# and
                       Standard.Character'Pos (Source (Pointer + 1)) in 16#80#..16#BF# and
                       Standard.Character'Pos (Source (Pointer + 2)) in 16#80#..16#BF# and
                       Standard.Character'Pos (Source (Pointer + 3)) in 16#80#..16#BF#
                     then
                        return Pointer < Last - 3;
                     elsif
                       Standard.Character'Pos (Source (Pointer + 0)) = 16#F4# and
                       Standard.Character'Pos (Source (Pointer + 1)) in 16#80#..16#8F# and
                       Standard.Character'Pos (Source (Pointer + 2)) in 16#80#..16#BF# and
                       Standard.Character'Pos (Source (Pointer + 3)) in 16#80#..16#BF#
                     then
                        return Pointer < Last - 3;
                     else
                        return False;
                     end if;
                  else
                     return False;
                  end if;
               else
                  return False;
               end if;
            else
               return False;
            end if;
         else
            return False;
         end if;
      end Is_Valid_UTF8_Code_Point;

      function Is_Valid_UTF8_Code_Point (Source      : String_T;
                                         Pointer     : Int32_T) return Boolean is
      begin
         return Is_Valid_UTF8_Code_Point (Source, Positive (Pointer));
      end Is_Valid_UTF8_Code_Point;

      procedure Get (Source      : String_T;
                     Pointer     : in out Positive;
                     Value       : out Aida.UTF8_Code_Point.T)
      is
         Accum : Aida.UTF8_Code_Point.T'Base;
         Code  : Aida.UTF8_Code_Point.T'Base;
      begin
         Code := Aida.UTF8_Code_Point.T (Standard.Character'Pos (Source (Pointer)));

         case Code is
         when 0..16#7F# => -- 1 byte (ASCII)
            Value   := Code;
            Pointer := Pointer + 1;
         when 16#C2#..16#DF# => -- 2 bytes
            Accum := (Code and 16#1F#) * 2**6;
            Code := Aida.UTF8_Code_Point.T (Standard.Character'Pos (Source (Pointer + 1)));
            Value   := Accum or (Code and 16#3F#);
            Pointer := Pointer + 2;
         when 16#E0# => -- 3 bytes
            Code := Aida.UTF8_Code_Point.T (Standard.Character'Pos (Source (Pointer + 1)));
            Accum := (Code and 16#3F#) * 2**6;
            Code := Aida.UTF8_Code_Point.T (Standard.Character'Pos (Source (Pointer + 2)));
            Value   := Accum or (Code and 16#3F#);
            Pointer := Pointer + 3;
         when 16#E1#..16#EF# => -- 3 bytes
            Accum := (Code and 16#0F#) * 2**12;
            Code := Aida.UTF8_Code_Point.T (Standard.Character'Pos (Source (Pointer + 1)));
            Accum := Accum or (Code and 16#3F#) * 2**6;
            Code := Aida.UTF8_Code_Point.T (Standard.Character'Pos (Source (Pointer + 2)));
            Value   := Accum or (Code and 16#3F#);
            Pointer := Pointer + 3;
         when 16#F0# => -- 4 bytes
            Code := Aida.UTF8_Code_Point.T (Standard.Character'Pos (Source (Pointer + 1)));
            Accum := (Code and 16#3F#) * 2**12;
            Code := Aida.UTF8_Code_Point.T (Standard.Character'Pos (Source (Pointer + 2)));
            Accum := Accum or (Code and 16#3F#) * 2**6;
            Code := Aida.UTF8_Code_Point.T (Standard.Character'Pos (Source (Pointer + 3)));
            Value   := Accum or (Code and 16#3F#);
            Pointer := Pointer + 4;
         when 16#F1#..16#F3# => -- 4 bytes
            Accum := (Code and 16#07#) * 2**18;
            Code := Aida.UTF8_Code_Point.T (Standard.Character'Pos (Source (Pointer + 1)));
            Accum := Accum or (Code and 16#3F#) * 2**12;
            Code := Aida.UTF8_Code_Point.T (Standard.Character'Pos (Source (Pointer + 2)));
            Accum := Accum or (Code and 16#3F#) * 2**6;
            Code := Aida.UTF8_Code_Point.T (Standard.Character'Pos (Source (Pointer + 3)));
            Value   := Accum or (Code and 16#3F#);
            Pointer := Pointer + 4;
         when 16#F4# => -- 4 bytes
            Accum := (Code and 16#07#) * 2**18;
            Code := Aida.UTF8_Code_Point.T (Standard.Character'Pos (Source (Pointer + 1)));
            Accum := Accum or (Code and 16#3F#) * 2**12;
            Code := Aida.UTF8_Code_Point.T (Standard.Character'Pos (Source (Pointer + 2)));
            Accum := Accum or (Code and 16#3F#) * 2**6;
            Code := Aida.UTF8_Code_Point.T (Standard.Character'Pos (Source (Pointer + 3)));
            Value   := Accum or (Code and 16#3F#);
            Pointer := Pointer + 4;
         when others =>
            raise Constraint_Error; -- This exception will never be raised if pre-conditions are met.
         end case;
      end Get;

      procedure Get (Source      : String_T;
                     Pointer     : in out Int32_T;
                     Value       : out Aida.UTF8_Code_Point.T) is
      begin
         Get (Source, Positive (Pointer), Value);
      end Get;

      function Length (Source : String_T) return Nat32_T is
         Count : Nat32_T := 0;
         Accum : Aida.UTF8_Code_Point.T;
         pragma Unreferenced (Accum);

         Index : Integer := Source'First;
      begin
         while Index <= Source'Last loop
            if Is_Valid_UTF8_Code_Point (Source, Index) then
               Get (Source, Index, Accum);
               Count := Count + 1;
            else
               exit;
            end if;
         end loop;
         return Count;
      end Length;

      procedure Put (Destination : in out String_T;
                     Pointer     : in out Positive;
                     Value       : Aida.UTF8_Code_Point.T) is
      begin
         if Value <= 16#7F# then
            Destination (Pointer) := Standard.Character'Val (Value);
            Pointer := Pointer + 1;
         elsif Value <= 16#7FF# then
            Destination (Pointer) := Standard.Character'Val (16#C0# or Value / 2**6);
            Destination (Pointer + 1) := Standard.Character'Val (16#80# or (Value and 16#3F#));
            Pointer := Pointer + 2;
         elsif Value <= 16#FFFF# then
            Destination (Pointer) := Standard.Character'Val (16#E0# or Value / 2**12);
            Destination (Pointer + 1) := Standard.Character'Val (16#80# or (Value / 2**6 and 16#3F#));
            Destination (Pointer + 2) := Standard.Character'Val (16#80# or (Value and 16#3F#));
            Pointer := Pointer + 3;
         else
            Destination (Pointer) := Standard.Character'Val (16#F0# or Value / 2**18);
            Destination (Pointer + 1) := Standard.Character'Val (16#80# or (Value / 2**12 and 16#3F#));
            Destination (Pointer + 2) := Standard.Character'Val (16#80# or (Value / 2**6 and 16#3F#));
            Destination (Pointer + 3) := Standard.Character'Val (16#80# or (Value and 16#3F#));
            Pointer := Pointer + 4;
         end if;
      end Put;

      procedure Put (Destination : in out String_T;
                     Pointer     : in out Int32_T;
                     Value       : Aida.UTF8_Code_Point.T) is
      begin
         Put (Destination, Positive (Pointer), Value);
      end Put;

      function To_Lowercase (Value : String_T) return String_T is
         Result : String_T (1..Value'Length);
         From   : Integer := Value'First;
         To     : Integer := 1;
         Code   : Aida.UTF8_Code_Point.T;
      begin
         while From <= Value'Last loop
            Aida.UTF8.Get (Value, From, Code);
            Code := To_Lowercase (Code);
            Aida.UTF8.Put (Result, To, Code);
         end loop;
         return Result (1..Positive (To - 1));
         --     exception
         --        when Layout_Error =>
         --           if From > Value'Last then
         --              return Result (1..To - 1) & Image (Code);
         --           else
         --              return
         --              (  Result (1..To - 1)
         --              &  Image (Code)
         --              &  To_Lowercase (Value (From..Value'Last))
         --              );
         --           end if;
      end To_Lowercase;

      function To_Uppercase (Value : String_T) return String_T is
         Result : String_T (1..Value'Length);
         From   : Integer := Value'First;
         To     : Integer := 1;
         Code   : Aida.UTF8_Code_Point.T;
      begin
         while From <= Value'Last loop
            Aida.UTF8.Get (Value, From, Code);
            Code := To_Uppercase (Code);
            Aida.UTF8.Put (Result, To, Code);
         end loop;
         return Result (1..To - 1);
         --     exception
         --        when Layout_Error =>
         --           if From > Value'Last then
         --              return Result (1..To - 1) & Image (Code);
         --           else
         --              return
         --              (  Result (1..To - 1)
         --              &  Image (Code)
         --              &  To_Uppercase (Value (From..Value'Last))
         --              );
         --           end if;
      end To_Uppercase;

   end UTF8;


end Aida;
