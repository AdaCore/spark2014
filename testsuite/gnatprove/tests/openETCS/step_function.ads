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

package Step_Function is pragma SPARK_Mode (On);
   type Num_Delimiters_Range is range 0 .. 10;

   type Function_Range is new Natural;

   type Delimiter_Entry is record
      Delimiter : Function_Range;
      Value : Float;
   end record;

   type Delimiter_Values is array (Num_Delimiters_Range)
     of Delimiter_Entry;

   type Step_Function_t is record
      Number_Of_Delimiters : Num_Delimiters_Range;
      Step : Delimiter_Values;
   end record;

   function Min(X1, X2 : Float) return Float
   with Post => (if X1 <= X2 then Min'Result = X1 else Min'Result = X2);

   function Is_Valid(SFun : Step_Function_t) return Boolean is
     (SFun.Step(0).Delimiter = Function_Range'First
      and
        (for all i in 0..(SFun.Number_Of_Delimiters - 1) =>
           (SFun.Step(i+1).Delimiter > SFun.Step(i).Delimiter)));

   function Has_Same_Delimiters(SFun1, SFun2 : Step_Function_t) return Boolean
   is
     (SFun1.Number_Of_Delimiters = SFun2.Number_Of_Delimiters
      and (for all i in 1.. SFun1.Number_Of_Delimiters =>
           SFun1.Step(i).Delimiter = SFun2.Step(i).Delimiter));

   function Get_Value(SFun : Step_Function_t; X: Function_Range) return Float
   with Pre => Is_Valid(SFun),
   Post => ((for some i in
               Num_Delimiters_Range'First..(SFun.Number_Of_Delimiters - 1) =>
               (SFun.Step(i).Delimiter <= X
                and X < SFun.Step(i+1).Delimiter
                and Get_Value'Result = SFun.Step(i).Value))
            or
              (X >= SFun.Step(SFun.Number_Of_Delimiters).Delimiter
               and Get_Value'Result
               = SFun.Step(SFun.Number_Of_Delimiters).Value));

   function Minimum_Until_Point(SFun : Step_Function_t; X: Function_Range)
                                return Float
   with
     Pre => Is_Valid(SFun),
   Post =>
   -- returned value is the minimum until the point X
     (for all i in Num_Delimiters_Range'First..SFun.Number_Of_Delimiters =>
        (if X >= SFun.Step(i).Delimiter then
         Minimum_Until_Point'Result <= SFun.Step(i).Value))
     and
   -- returned value is a value of the step function until point X
     ((for some i in Num_Delimiters_Range'First..SFun.Number_Of_Delimiters =>
         (X >= SFun.Step(i).Delimiter
          and
            (Minimum_Until_Point'Result = SFun.Step(i).Value))));

   procedure Index_Increment(SFun: Step_Function_t;
                             i: in out Num_Delimiters_Range;
                             scan: in out Boolean)
   with Post =>
     (if i'Old < SFun.Number_Of_Delimiters then
        (i = i'Old + 1 and scan = scan'Old)
      else
        (i = i'Old and scan = False));

   -- Note: In the following Post condition, it would be better to tell that
   -- Merge is the minimum of both SFun1 and SFun2 for all possible input
   -- values, but I'm not sure that can be proved
   procedure Restrictive_Merge(SFun1, SFun2 : in Step_Function_t;
                               Merge : out Step_Function_t)
   with Pre => Is_Valid(SFun1) and Is_Valid(SFun2)
     and SFun1.Number_Of_Delimiters + SFun2.Number_Of_Delimiters <=
       Num_Delimiters_Range'Last,
   Post =>
   -- Output is valid step function
   Is_Valid(Merge)
   -- all SFun1 delimiters are valid delimiters in Merge
     and (for all i in Num_Delimiters_Range'First..SFun1.Number_Of_Delimiters =>
            (for some j in
               Num_Delimiters_Range'First..Merge.Number_Of_Delimiters =>
                 (Merge.Step(j).Delimiter = SFun1.Step(i).Delimiter)))
   -- all SFun2 delimiters are valid delimiters in Merge
     and (for all i in Num_Delimiters_Range'First..SFun2.Number_Of_Delimiters =>
            (for some j in
               Num_Delimiters_Range'First..Merge.Number_Of_Delimiters =>
                 (Merge.Step(j).Delimiter = SFun2.Step(i).Delimiter)))
   -- for all delimiters of Merge, its value is the minimum of SFun1 and SFun2
     and (for all i in Num_Delimiters_Range'First..Merge.Number_Of_Delimiters =>
            (Merge.Step(i).Value = Min(Get_Value(SFun1,
                                                 Merge.Step(i).Delimiter),
                                       Get_Value(SFun2,
                                                 Merge.Step(i).Delimiter))));
end Step_Function;
