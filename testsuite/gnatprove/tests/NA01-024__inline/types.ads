
package Types is
   pragma SPARK_Mode;


   subtype Float_1_T is Float;

   subtype Float_2_T is Float;

   type Float_Range_T is digits 7 range -180.0 .. 180.0;

   type Int_Range_T is range -30_000 .. 30_000;

   type Record_T is
      record
         A : Float_Range_T;
         B   : Int_Range_T;
         C   : Int_Range_T;
         D   : Int_Range_T;
         E   : Int_Range_T;
      end record;



end Types;
