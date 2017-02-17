package body Super is

   function Super_Length (Source : Super_String) return Natural is
   begin
      return Source.Current_Length;
   end Super_Length;

end Super;
