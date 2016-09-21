package Delayed_Aspects is
   function Is_Valid (X : Integer) return Boolean is (X > 0) with
   SPARK_Mode => Off;

   type Good is private;

   type Bad is new Integer with Predicate => Is_Valid (Integer (Bad));

   function Is_Valid_2 (X : Integer) return Boolean;

   type Good_2 is private;

   type Bad_2 is new Integer with Predicate => Is_Valid_2 (Integer (Bad_2));
private
   type Good is new Integer with Predicate => Is_Valid (Integer (Good));

   Y : Integer := 0;

   function Is_Valid_2 (X : Integer) return Boolean is (X = Y);

   type Good_2 is new Integer with Predicate => Is_Valid_2 (Integer (Good_2));
end Delayed_Aspects;
