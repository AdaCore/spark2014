with Unchecked_Conversion;

package body Convert is

   function id (Left : A) return B

   is
     function A_To_B is
       new Unchecked_Conversion (Source => A, Target => B);
   begin
      return A_To_B (S => Left);
      --             ^^^^^^^^^ explicit parameter association
   end id;

end Convert;
