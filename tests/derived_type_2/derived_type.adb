package body Derived_Type is

   procedure Work_Day
     (ToDay : out Week_Day;
      WeDay : out Week_End)
   is
   begin
      ToDay := Mon;
      Weday := Sat;
   end Work_Day;

end Derived_Type;
