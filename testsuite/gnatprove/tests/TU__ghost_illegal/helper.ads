package Helper is
   generic
      type Elem is private;
   function Return_First (A, B : Elem ; Choice : Boolean) return Elem;
end Helper;
