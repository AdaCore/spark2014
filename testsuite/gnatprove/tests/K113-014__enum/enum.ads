package Enum is

   type Day is (Mon, Tue, Wed, Thu, Fri, Sat, Sun);

   function Sunday return Day
      with Post => (Sunday'Result = Sun);

end Enum;
