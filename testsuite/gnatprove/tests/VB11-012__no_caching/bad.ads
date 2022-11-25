pragma SPARK_Mode;

package Bad is

   type Value_Type is new Integer with No_Caching;

   X : Integer with No_Caching;

   type T is new Integer with Volatile;
   type T2 is new T with No_Caching;
   subtype T3 is T with No_Caching;

end Bad;
