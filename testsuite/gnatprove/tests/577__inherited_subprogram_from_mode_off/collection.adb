package body Collection with SPARK_Mode is

   package body Bad_Descendants_Off with SPARK_Mode => Off is
      function F (X : Good_Descendant) return Integer is (42);
      procedure P (X : Good_Descendant) is
      begin
         null;
      end P;
      function Create return Good_Descendant is
         Y : Root_Pack.Root'Class := In_Private.Witness;
      begin
         Y := Root_Pack.Create;
         return (In_Private.Child (Y) with null record);
      end Create;
      function Create return Bad_Over_Good is
        (Good_Descendant'(Create) with null record);
   end Bad_Descendants_Off;

   package body In_Private is
      function Create return Missing_Link is (null record);
   end In_Private;

   package body Bad_Descendants_Hide with SPARK_Mode => Off is
      function F (X : Good_Descendant) return Integer is (42);
      procedure P (X : Good_Descendant) is
      begin
         null;
      end P;
      function Create return Good_Descendant is
         Y : Root_Pack.Root'Class := In_Private.Witness;
      begin
         Y := Root_Pack.Create;
         return (In_Private.Child (Y) with null record);
      end Create;
      function Create return Bad_Over_Good is
        (Good_Descendant'(Create) with null record);
   end Bad_Descendants_Hide;

end Collection;
