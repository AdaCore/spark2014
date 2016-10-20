package P is pragma SPARK_Mode (On);

   Global : Boolean := True;

   subtype S1 is Boolean
   with Dynamic_Predicate => S1 and Global;
   -- predicate depends on a global variable; should be reported

private
   pragma SPARK_Mode (Off);

   subtype S2 is Boolean
   with Dynamic_Predicate => S2 and Global;
   -- predicate depends on a global variable; should NOT be reported

end;
