package Derived_Type is
   type Day_Name is (Mon, Tue, Wed, Thu, Fri, Sat, Sun);
   type Week_Day is new Day_Name range Mon .. Fri;
   type Week_End is new Day_Name range Sat .. Sun;

   procedure Work_Day
     (ToDay : out Week_Day;
      WeDay : out Week_End);

end Derived_Type;
