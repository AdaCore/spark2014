package Days
  with SPARK_Mode
is
   type Day is
     (Monday, Tuesday, Wednesday, Thursday, Friday, Saturday, Sunday);

   subtype T_Day is Day with Static_Predicate => T_Day in Tuesday | Thursday;

   procedure Next (D : in out Day);

   procedure Next_T (D : in out T_Day);

end Days;
