package body Dates with SPARK_Mode is

  type Date_Triple_Type is record
     Year  : Year_Number;
  end record;

  function Split (Days : Date_Range) return Date_Triple_Type is
  begin
     return T : Date_Triple_Type do
        -- T := (Year => 1970); -- Why is this rejected?
        T.Year := 1970;
     end return;
  end Split;

  function Split (Date : Date_Type) return Date_Triple_Type is
    (Split (Date.Day_Of_Common_Era));

end Dates;
