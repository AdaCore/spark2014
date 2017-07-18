package Clocks with SPARK_Mode is

   pragma Pure;

   --  For representing a time of day, such as '01:23:45'.

   --------------------------------
   -- Hours, minutes and seconds --
   --------------------------------

   type Hour_Number   is new Integer range 0 .. 23;
   type Minute_Number is new Integer range 0 .. 59;
   type Second_Number is new Integer range 0 .. 59;

   type Clock_Triple_Type is record
      Hour   : Hour_Number;
      Minute : Minute_Number;
      Second : Second_Number;
   end record;
   --  A raw time of day such as '23:45:15'.

   ------------
   -- Clocks --
   ------------

   type Clock_Type is private;
   --  Represents a time of day such as '12:34:56'.

   function Clock_Of (Triple : Clock_Triple_Type) return Clock_Type;
   --  Form a clock out of an hour, minute and second.

   function Split (Clock : Clock_Type) return Clock_Triple_Type with Inline;
   --  Returns the clock in Hour-Minute-Second form.

   type Second_Count is new Integer;
   subtype Day_Range is Second_Count range 0 .. 24 * 60 * 60 - 1;

   -----------------
   -- Correctness --
   -----------------

   package Correctness with Ghost is

      --  Assert the correctness of the package.

      function Clock_Of_Inverse_Of_Split (Clock : Clock_Type) return Boolean
        is (True) with Post => Clock_Of_Inverse_Of_Split'Result and
          Clock_Of (Split (Clock)) = Clock;
      --  Assert that Clock_Of is a left inverse of Split.

      function Split_Inverse_Of_Clock_Of (Triple : Clock_Triple_Type)
        return Boolean is (True) with Post => Split_Inverse_Of_Clock_Of'Result
          and Split (Clock_Of (Triple)) = Triple;
      --  Assert that Split is a left inverse of Clock_Of.

   end Correctness;

private

   type Clock_Type is record
      Day_Second : Day_Range;
   end record;

   function Clock_Of (Triple : Clock_Triple_Type) return Clock_Type is
     ((Day_Second => Day_Range (Triple.Hour) * One_Hour +
                     Day_Range (Triple.Minute) * One_Minute +
                     Day_Range (Triple.Second)));

   function Split (Clock : Clock_Type) return Clock_Triple_Type is
     ((Hour   => Hour_Number (Second_Of_Day (Clock) / One_Hour),
       Minute => Minute_Number
         ((Second_Of_Day (Clock) mod One_Hour) / One_Minute),
       Second => Second_Number (Second_Of_Day (Clock) mod One_Minute)));

end Clocks;
