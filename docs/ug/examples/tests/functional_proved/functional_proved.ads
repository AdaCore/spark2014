pragma Assertion_Policy (Pre => Check);

package Functional_Proved with
  SPARK_Mode
is
   procedure Seen_One (X : Integer) with
     Pre  => X >= 0 and then   --  AoRTE
             Invariant,        --  invariant checking
     Post => Invariant,        --  invariant checking
     Contract_Cases =>         --  full functional
       (X > Max_Value_Seen =>
          --  max value updated
          Max_Value_Seen = X and
          Second_Max_Value_Seen = Max_Value_Seen'Old,
        X > Second_Max_Value_Seen and
        X < Max_Value_Seen =>
          --  second max value updated
          Max_Value_Seen = Max_Value_Seen'Old and
          Second_Max_Value_Seen = X,
        X = Max_Value_Seen or
        X <= Second_Max_Value_Seen =>
          --  no value updated
          Max_Value_Seen = Max_Value_Seen'Old and
          Second_Max_Value_Seen = Second_Max_Value_Seen'Old);

   procedure Seen_Two (X, Y : Natural) with
     Pre  => X < Y and then               --  defensive programming
             Invariant,                   --  invariant checking
     Post => Invariant and then           --  invariant checking
             Max_Value_Seen > 0 and then  --  partial functional
             Max_Value_Seen /= Second_Max_Value_Seen;

   function Invariant return Boolean;

   function Max_Value_Seen return Integer;

   function Second_Max_Value_Seen return Integer;

end Functional_Proved;
