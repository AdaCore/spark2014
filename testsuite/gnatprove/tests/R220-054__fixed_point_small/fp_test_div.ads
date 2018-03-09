package FP_Test_Div with
  SPARK_Mode
is
   type FP1 is delta 1.0 / 3.0 range -10.0 .. 10.0 with Small => 1.0 / 3.0;
   type FP2 is delta 1.0 / 5.0 range 1.0 .. 10.0 with Small => 1.0 / 5.0;
   type FP3 is delta 1.0 / 15.0 range -10.0 .. 10.0 with Small => 1.0 / 15.0;
   type FP4 is delta 1.0 / 30.0 range -10.0 .. 10.0 with Small => 1.0 / 30.0;

   procedure Test (X : FP1; Y : FP2; U : out FP3; V : out FP4);

   procedure Test1 (X : FP1; Y : FP2; U : out FP3; V : out FP4) with
     Pre  => X = 1.0 and Y = 1.0,
     Post => U = 1.0 and V = 1.0;

   procedure Test2 (X : FP1; Y : FP2; U : out FP3; V : out FP4) with
     Pre  => abs X <= 8.0 and abs Y <= 2.0,
     Post => abs U <= 4.0 and abs V <= 4.0;

end FP_Test_Div;
