pragma Assertion_Policy (Pre => Check);

package Integrity with
  SPARK_Mode
is
   procedure Seen_One (X : Integer) with
     Pre => X >= 0;  --  AoRTE

   procedure Seen_Two (X, Y : Natural) with
     Pre => X < Y;  --  defensive programming

end Integrity;
