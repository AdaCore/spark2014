package Super is 

   Max_Length : constant Positive := 10;
   type Super_String is record
      Current_Length : Natural := 0;
      Data           : String (1 .. Max_Length);
   end record;

   function Super_Length (Source : Super_String) return Natural;

end Super;
