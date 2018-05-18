package Stringlen with SPARK_Mode is
   subtype StringF1 is String with
     Predicate => StringF1'First = 1;
   subtype StringF1L20 is StringF1 with
     Predicate => StringF1L20'Last <= 20;
end StringLen;
