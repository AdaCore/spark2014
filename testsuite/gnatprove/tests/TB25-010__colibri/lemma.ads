generic
   type Fl is digits <>;
   Fl_Last_Sqrt : Fl;
package Lemma with SPARK_Mode is

   procedure Lemma_Div_Left_Is_Monotonic
     (Val1 : Fl;
      Val2 : Fl;
      Val3 : Fl)
     with
       Global => null,
       Pre =>
         (Val1 in 0.0 .. Fl_Last_Sqrt) and then
         ((Val2 in 1.0 / Fl_Last_Sqrt .. Fl'Last and then
           Val3 in 1.0 / Fl_Last_Sqrt .. Fl'Last) or else
          (Val2 in Fl'First .. -1.0 / Fl_Last_Sqrt and then
           Val3 in Fl'First .. -1.0 / Fl_Last_Sqrt)) and then
         Val2 <= Val3,
       Post => Val1 / Val3 <= Val1 / Val2; 

end Lemma;
