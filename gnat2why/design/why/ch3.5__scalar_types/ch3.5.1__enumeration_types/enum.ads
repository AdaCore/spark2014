package Enum is

   type Day is (Mon, Tue, Wed, Thu, Fri, Sat, Sun);

   type Some_A is ('A', A);

   type Name_Clash is (Mon, A);

   subtype Weekday is Day range Mon .. Fri;

end Enum;
