package body Sample is

   procedure Study_Case (Nb_Of_Fp     : in     Nb_Type;
                         Nb_Of_Pp     : in     Nb_Type;
                         Delta_Time   : in     Delta_Time_Type;
                         Time         : in out Float)
     with SPARK_Mode => On
   is
      D    : D_Time_Type;
      T_Fp : Float range Float'First .. Float'Pred (Float'Last);
      T_Pp : Float;
      Tmp1 : Float range 0.0 .. 200.0;
      Tmp2 : Float range 0.0 .. 50.0;
   begin

     D    := Float (Nb_Of_Fp + Nb_Of_Pp) * Delta_Time;
     T_Fp := Time - (D / 2.0);
     Tmp1 := Float (Nb_Of_Fp) * Delta_Time;
     T_Pp := T_Fp + Tmp1;
     Tmp2 := 0.5 * Float (Nb_Of_Fp) * Delta_Time;
     Time := T_Pp + Tmp2;

   end Study_Case;

   procedure Simple_Case (Nb         : in     Nb_Float_Type;
                          Time       : in out Float)
     with SPARK_Mode => On
   is
      Tmp : Float range 0.0 .. 8.0 := 0.5 * Nb;
   begin

     Time := Time + Tmp;
   end Simple_Case;

end Sample;
