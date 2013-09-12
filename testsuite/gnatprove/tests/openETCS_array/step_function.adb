--  copyright 2013 David MENTRE <d.mentre@fr.merce.mee.com>
--                                 -- Mitsubishi Electric R&D Centre Europe
--
--  Licensed under the EUPL V.1.1 or - as soon they will be approved by
--  the European Commission - subsequent versions of the EUPL (the
--  "Licence");
--  You may not use this work except in compliance with the Licence.
--
--  You may obtain a copy of the Licence at:
--
--    http://joinup.ec.europa.eu/software/page/eupl/licence-eupl
--
--  Unless required by applicable law or agreed to in writing, software
--  distributed under the Licence is distributed on an "AS IS" basis,
--  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
--  implied.
--
--  See the Licence for the specific language governing permissions and
--  limitations under the Licence.

package body Step_Function is pragma SPARK_Mode (On);
   function Min(X1, X2 : Float) return Float is
   begin
      if X1 <= X2 then return X1; else return X2; end if;
   end;

   function Get_Value(SFun : Step_Function_t; X: Function_Range) return Float is
   begin
      for i in Num_Delimiters_Range'First..(SFun.Number_Of_Delimiters - 1) loop
         Pragma Assert (for all j in 1..i =>
                          X >= SFun.Step(j).Delimiter);
         if X >= SFun.Step(i).Delimiter and X < SFun.Step(i + 1).Delimiter then
            return SFun.Step(i).Value;
         end if;
      end loop;

      return SFun.Step(SFun.Number_Of_Delimiters).Value;
   end Get_Value;

   function Minimum_Until_Point(SFun : Step_Function_t; X: Function_Range)
                                return Float is
      min : Float := SFun.Step(Num_Delimiters_Range'First).Value;
   begin
      for i in Num_Delimiters_Range'First .. SFun.Number_Of_Delimiters loop
         Pragma Loop_Invariant
           (for all j in Num_Delimiters_Range'First..i-1 =>
              (if X >= SFun.Step(j).Delimiter then
               min <= SFun.Step(j).Value));
         Pragma Loop_Invariant
           (for some j in Num_Delimiters_Range'First..i =>
              (X >= SFun.Step(j).Delimiter
               and
                 min = SFun.Step(j).Value));

         if X >= SFun.Step(i).Delimiter then
            if SFun.Step(i).Value < min then min := SFun.Step(i).Value; end if;
--           else
--              Pragma Assert
--                (for all j in i+1..SFun.Number_Of_Delimiters =>
--                   SFun.Step(j-1).Delimiter < SFun.Step(j).Delimiter);
--              Pragma Assert (X < SFun.Step(i).Delimiter);
--              Pragma Assert
--                (for all j in i..SFun.Number_Of_Delimiters =>
--                   X < SFun.Step(j).Delimiter);
--
--              return min;
         end if;
      end loop;

      return min;
   end Minimum_Until_Point;

   procedure Index_Increment(SFun: Step_Function_t;
                             i: in out Num_Delimiters_Range;
                             scan: in out Boolean) is
   begin
      if i < SFun.Number_Of_Delimiters then
         i := i + 1;
      else
         scan := False;
      end if;
   end;

   procedure Restrictive_Merge(SFun1, SFun2 : in Step_Function_t;
                               Merge : out Step_Function_t) is
--     begin
--        null;
--     end;
      i1 : Num_Delimiters_Range := 0;
      i2 : Num_Delimiters_Range := 0;
      im : Num_Delimiters_Range := 0;
      scan_sfun1 : Boolean := True;
      scan_sfun2 : Boolean := True;
   begin
      Pragma Assert (SFun1.Step(0).Delimiter = SFun2.Step(0).Delimiter);
      loop
         -- im, i1 and i2 bounds
         Pragma Loop_Invariant (i1 >= 0 and i2 >= 0 and im >= 0);
         Pragma Loop_Invariant (i1 <= SFun1.Number_Of_Delimiters);
         Pragma Loop_Invariant (i2 <= SFun2.Number_Of_Delimiters);
         Pragma Loop_Invariant (i1 + i2 <= Num_Delimiters_Range'Last);
         Pragma Loop_Invariant (im <= Num_Delimiters_Range'Last);
         Pragma Loop_Invariant
          ((I1 = 0 and I2 = 0 and Im = 0)
             or else
           (I1 >= 1 and I2 >= 1 and Im >= 1 and
                Scan_SFun1 and Scan_SFun2 and Im <= I1 + I2 - 1)
             or else
           (I2 >= 1 and Im >= 1 and
              not Scan_SFun1 and Scan_SFun2 and Im <= i1 + I2)
             or else
           (I1 >= 1 and Im >= 1 and
              Scan_SFun1 and not Scan_SFun2 and Im <= i1 + I2));
         Pragma Loop_Invariant (Scan_Sfun1 or Scan_Sfun2);

         -- Merge is a valid step function until im
         Pragma Loop_Invariant (for all i in 1..im-1 =>
                                  Merge.Step(I-1).Delimiter < Merge.Step(I).Delimiter);
         Pragma Loop_Invariant
           (if Im > 0 then
              ((if Scan_Sfun1 then Merge.Step(Im-1).Delimiter < SFun1.Step(I1).Delimiter)
                 and then
               (if Scan_Sfun2 then Merge.Step(Im-1).Delimiter < SFun2.Step(I2).Delimiter)));

         -- All merged delimiters are coming from valid delimiter in SFun1 or
         -- SFun2
         Pragma Loop_Invariant
           (for all i in 0..(if Scan_Sfun1 then I1-1 else I1) =>
              ((for some j in 0..im-1 =>
                  SFun1.Step(i).Delimiter = Merge.Step(j).Delimiter)));
         Pragma Loop_Invariant
           (for all i in 0..(if Scan_Sfun2 then I2-1 else I2)=>
              ((for some j in 0..im-1 =>
                  SFun2.Step(i).Delimiter = Merge.Step(j).Delimiter)));

         -- Merged value at a delimiter is the minimum of both step functions
         Pragma Loop_Invariant
           (for all i in 0..im-1 =>
              Merge.Step(i).Value =
              Min(Get_Value(SFun1, Merge.Step(i).Delimiter),
                Get_Value(SFun2, Merge.Step(i).Delimiter)));

         if scan_sfun1 and scan_sfun2 then
            -- select on delimiter from SFun1 or SFun2
            if SFun1.Step(i1).Delimiter < SFun2.Step(i2).Delimiter then
               Merge.Step(im).Delimiter := SFun1.Step(i1).Delimiter;
               Merge.Step(im).Value :=
                 Min(Get_Value(SFun1, Merge.Step(im).Delimiter),
                     Get_Value(SFun2, Merge.Step(im).Delimiter));
               Index_Increment(SFun1, i1, scan_sfun1);

            elsif SFun1.Step(i1).Delimiter > SFun2.Step(i2).Delimiter then
               Merge.Step(im).Delimiter := SFun2.Step(i2).Delimiter;
               Merge.Step(im).Value :=
                 Min(Get_Value(SFun1, Merge.Step(im).Delimiter),
                     Get_Value(SFun2, Merge.Step(im).Delimiter));
               Index_Increment(SFun2, i2, scan_sfun2);

            else -- SFun1.Step(i1).Delimiter = SFun2.Step(i2).Delimiter
               Merge.Step(im).Delimiter := SFun1.Step(i1).Delimiter;
               Merge.Step(im).Value :=
                 Min(Get_Value(SFun1, Merge.Step(im).Delimiter),
                     Get_Value(SFun2, Merge.Step(im).Delimiter));
               Index_Increment(SFun1, i1, scan_sfun1);
               Index_Increment(SFun2, i2, scan_sfun2);
            end if;
         elsif scan_sfun1 then
            -- only use SFun1 delimiter
            Merge.Step(im).Delimiter := SFun1.Step(i1).Delimiter;
            Merge.Step(im).Value :=
              Min(Get_Value(SFun1, Merge.Step(im).Delimiter),
                  Get_Value(SFun2, Merge.Step(im).Delimiter));
            Index_Increment(SFun1, i1, scan_sfun1);
         else -- scan_sfun2
              -- only use SFun2 delimiter
               Merge.Step(im).Delimiter := SFun2.Step(i2).Delimiter;
               Merge.Step(im).Value :=
                 Min(Get_Value(SFun1, Merge.Step(im).Delimiter),
                     Get_Value(SFun2, Merge.Step(im).Delimiter));
            Index_Increment(SFun2, i2, scan_sfun2);
         end if;

         -- Pragma Assert (if scan_sfun1 or scan_sfun2 then im < i1 + i2);
         if Scan_Sfun1 or Scan_Sfun2 then
            im := im + 1;
            pragma Assert (for all I in 1..Im-2 =>
                             Merge.Step(I-1).Delimiter < Merge.Step(I).Delimiter);
            if Im > 1 then
               pragma Assert (Merge.Step(Im-2).Delimiter < Merge.Step(Im-1).Delimiter);
            end if;
         else
            exit;
         end if;
      end loop;

      Merge.Number_Of_Delimiters := im;
   end Restrictive_Merge;
end Step_Function;
