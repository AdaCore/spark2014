pragma SPARK_Mode;
procedure Ex is

   function Count (Source  : in String;
                   Pattern : in Character) return Natural is
   -- Returns the number of times Pattern occurs in Source
      Result : Natural := 0;
   begin
      for Index in Source'Range loop
         if Source (Index) = Pattern then
            Result := Result + 1;
         end if;
      end loop;
      return Result;
   end Count;

   The_Count   : Natural;

begin
   The_Count := Count (Source  => "How now brown cow",
                       Pattern => 'w');
end Ex;
