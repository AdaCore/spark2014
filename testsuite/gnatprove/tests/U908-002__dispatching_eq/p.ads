package P is
   type Object is tagged null record;

   function F (O1, O2 : Object) return Boolean is (True);

   function "=" (O1, O2 : Object) return Boolean is (True) with
      Post'Class => "="'Result and P.F (O1, O2) and F (O1, O2);

   type Child is new Object with record
      F : Integer;
   end record;

   function "=" (O1, O2 : Child) return Boolean is (True);
end P;
