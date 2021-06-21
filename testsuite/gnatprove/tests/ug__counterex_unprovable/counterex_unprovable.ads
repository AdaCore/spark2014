package Counterex_Unprovable with
  SPARK_Mode
is

   type Int is new Integer range -100 .. 100;

   function Double (X : Int) return Int with
     Pre  => abs X <= 10,
     Post => abs Double'Result <= 20;

   procedure Double_In_Call (X : in out Int) with
     Pre  => abs X <= 10,
     Post => X = 2 * X'Old;

   procedure Double_In_Loop (X : in out Int) with
     Pre  => abs X <= 10,
     Post => X = 2 * X'Old;

end Counterex_Unprovable;
