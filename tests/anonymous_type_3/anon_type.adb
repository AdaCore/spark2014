package body Anon_Type
is
   procedure Date_Format(ToDay1 , ToDay2 , ToDay3 : out Date)
   is
   begin
      -- Positional aggregate
      ToDay1     := (26, July, 2010);
      -- Named aggregate
      --Day_String => "Friday"
      ToDay2     := (Day => 26, Month => July,
                     Year => 2010);
      ToDay3     := (Month => July, Day => 26,
                     Year => 2010);
   end Date_Format;
end Anon_Type;
