package P with SPARK_Mode is
   task TT;
   X : Boolean with Part_Of => TT;

   protected PT is end;
   Y : Boolean with Part_Of => PT;
end;
