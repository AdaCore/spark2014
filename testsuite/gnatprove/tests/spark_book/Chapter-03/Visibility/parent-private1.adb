with Parent.Public1.Public2;
package body Parent.Private1 is

   function Convert (Value : in Parent_Int) return Private_Int is
   begin
      return Private_Int (Value);
   end Convert;

end Parent.Private1;
