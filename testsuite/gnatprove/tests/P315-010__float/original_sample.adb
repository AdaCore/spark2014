package body Original_Sample is

   procedure Study_Case (Nb_Of_Fp     : in     Nb_Type;
                         Nb_Of_Pp     : in     Nb_Type;
                         Delta_Time   : in     Delta_Time_Type;
                         Time         : in out Float)
     with SPARK_Mode => On
   is
      D    : D_Time_Type;
      T_Fp : Float;
      T_Pp : Float;
   begin

     D    := Float (Nb_Of_Fp + Nb_Of_Pp) * Delta_Time;
     T_Fp := Time - (D / 2.0);
     T_Pp := T_Fp + Float (Nb_Of_Fp) * Delta_Time;
     Time := T_Pp + 0.5 * Float (Nb_Of_Fp) * Delta_Time;

   end Study_Case;

   procedure Simple_Case (Nb         : in     Nb_Float_Type;
                          Time       : in out Float)
     with SPARK_Mode => On
   is
   begin

     Time := Time + 0.5 * Nb;

   end Simple_Case;

end Original_Sample;
