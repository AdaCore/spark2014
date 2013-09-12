package A is pragma SPARK_Mode (On);
   subtype T is Integer range 1 .. 10;
   function Any return T
      with Post => (Any'Result > 2);
end A;

