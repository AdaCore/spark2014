with Parent.Public1;
private package Parent.Private1 is
   A : constant Parent_Int := P; -- P is from private part of Parent
   type Private_Int is private;
   K : constant Private_Int;
   function Convert (Value : in Parent_Int) return Private_Int;
private
   type Private_Int is new Parent_Int;
   K : constant Private_Int := 45;
end Parent.Private1;
