package Funcs is
   type Root is tagged null record;

   function Valid (O : Root) return Boolean is (True)
     with Pre'Class => True;

   function Id (O : Root) return Root is (O)
     with Post => Valid (Root'Class (Id'Result));

end Funcs;
