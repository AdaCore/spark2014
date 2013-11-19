package P is
   pragma SPARK_Mode(On);

   procedure P (X : in out Integer)
      with Pre => X < Integer'Last;
end P;
