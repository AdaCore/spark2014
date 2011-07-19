package body Refi is

   function Arguments_From (Ignore_Non_Existing_Files : Boolean)
      return Integer
   is

      procedure Recurse (File_Name : String) is
      begin
         if Ignore_Non_Existing_Files then
            return;
         end if;
      end Recurse;

   begin
      return 0;
   end Arguments_From;

end Refi;
