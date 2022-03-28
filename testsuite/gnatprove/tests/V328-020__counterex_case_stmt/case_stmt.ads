package Case_Stmt is

  --  Int

  type Index is range 1 .. 20;

  subtype Tenths is Index range 10 .. 20;

  subtype Ten_Fourteen is Tenths range 10 .. 14;

  subtype Fifteen_Twenty is Tenths
    with Static_Predicate => Fifteen_Twenty in 15 .. 20;

  subtype Lower_Than_Five is Index
    with Static_Predicate => Lower_Than_Five in 1 .. 4;

  subtype Five_To_Nine is Index
    with Static_Predicate => (Five_To_Nine not in Lower_Than_Five) and
                             not (Five_To_Nine in Tenths);

  --  Days

  type Day is (Mon, Tue, Wed, Thu, Fri, Sat, Sun);

  subtype Weekday is Day range Mon .. Fri;

  subtype Weekend is Day
    with Static_Predicate => Weekend in Sat | Sun;

  subtype Wednesday is Day range Mon .. Sun
    with Static_Predicate => Wednesday in Wed .. Wed;

  type Action is (Work, Party, Sleep, Nothing);

  --  Functions

  procedure Index_Range (I : Index);
  --  Case statement with Index range in choice expression

  procedure Index_Subtype (K : Index);
  --  Subtype (range and static predicate) in choice expression

  procedure Week_Range (D : Day);
  --  Case statement with enum range in choice expression

  procedure Week_Static_Predicate (D : Day);
  --  Subtype with static predicate in choice expr

end Case_Stmt;
