package P with SPARK_Mode is
   X : Boolean with Part_Of => TT;
   task TT;

   Y : Boolean with Part_Of => PT;
   protected PT is end;
end;
