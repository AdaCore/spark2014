package S is

   generic
      type Element is private;
   function Id (E : Element) return Element with Post => Id'Result = E;

   function Id (E : Element) return Element is (E);

end S;
