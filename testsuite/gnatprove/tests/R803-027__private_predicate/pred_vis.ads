package Pred_Vis with SPARK_Mode is
   type Root is tagged record
      F1 : Integer;
      G1 : Integer;
      G2 : Integer;
   end record
     with Predicate => F1 > 0;
   type Child is new Root with record
      F2 : Integer;
   end record
     with Predicate => F2 > 0 and F1 < 100;
   type Grand_Child is new Root with private;
   type Grand_Grand_Child is new Root with private
     with Predicate => G2 > 15;
   type Grand_Grand_Child_2 is new Grand_Child with private;
   type Grand_Grand_Child_3 is new Child with private
     with Dynamic_Predicate => Grand_Grand_Child_3.G2 > 15;

private
   pragma SPARK_Mode (Off);
   type Grand_Child is new Child with null record
     with Predicate => G1 > 10;
   type Grand_Child_P is new Grand_Child with null record;
   type Grand_Grand_Child is new Grand_Child_P with null record;
   type Grand_Grand_Child_2 is new Grand_Child_P with null record
     with Dynamic_Predicate => G2 > 15;
   type Grand_Grand_Child_3 is new Grand_Child_P with null record;
end Pred_Vis;
