package Pred_Vis with SPARK_Mode is
   type Root is tagged record
      F1 : Integer;
      G1 : Integer;
      G2 : Integer;
   end record
     with Predicate => F1 > 0;
   type Child is new Root with private
     with Dynamic_Predicate => Child.G2 > 15;
   type Child_2 is new Root with private
     with Dynamic_Predicate => Child_2.G2 > 15;
   type Child_3 is new Root with private;
   pragma Predicate (Entity => Child_3, Check => Child_3.G2 > 15);

private
   pragma SPARK_Mode (Off);
   type Child is new Root with null record
     with Predicate => G1 > 10;
   type Child_2 is new Root with null record;
   pragma Predicate (Entity => Child_2, Check => G1 > 10);
   type Child_3 is new Root with null record
     with Dynamic_Predicate => Child_3.G1 > 10;
end Pred_Vis;
