package Lemmas with SPARK_Mode, Ghost is

   subtype T is Integer range 0 .. 1000;

   procedure Mult_Mono (A, B, C : T)
   with
     Global => null,
     Pre    => A <= B,
     Post   => A * C <= B * C;

end Lemmas;
