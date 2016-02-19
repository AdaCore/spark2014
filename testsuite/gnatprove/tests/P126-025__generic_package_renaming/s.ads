package S is

   generic
      type Element is private;
   package Simple is
      function Id (E : Element) return Element is (E);
   end Simple;

end S;
