package body Sum_Elem with
  SPARK_Mode
is
   procedure Local (P : Partition; X : Partition_Index) is
   begin
      pragma Assert (Element (P, X).First + Element (P, X).Last in Index);
   end Local;

   procedure Main is
   begin
      Append (P, Interval'(First => 1, Last => 1));
      Local (P, 0);
   end Main;
end Sum_Elem;
