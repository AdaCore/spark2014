with SPARK.Containers.Formal.Unbounded_Ordered_Maps;
with SPARK.Containers.Functional.Sets;
with SPARK.Big_Intervals; use SPARK.Big_Intervals;

package body P with SPARK_Mode is
   procedure Formal_Maps is
      package Maps is new SPARK.Containers.Formal.Unbounded_Ordered_Maps
        (Key_Type       => Positive,
         Element_Type => Integer);
      type Map is new Maps.Map;
      use all type Map;

      M : Map;
   begin
      Insert (M, 1, 1);
      declare
         C : constant Map := M;
      begin
         for K of C loop
            null;
         end loop;
      end;
   end Formal_Maps;

   procedure Functional_Sets is
      package Sets is new SPARK.Containers.Functional.Sets
        (Element_Type => Integer);
      use Sets;

      S : Set;
   begin
      S := Add (S, 1);

      for Subset of Iterate (S) loop
         null;
      end loop;
   end Functional_Sets;

   procedure Big_Intervals is
   begin
      for I in Interval'(First => 1, Last => 2) loop
         null;
      end loop;
   end Big_Intervals;
end P;
