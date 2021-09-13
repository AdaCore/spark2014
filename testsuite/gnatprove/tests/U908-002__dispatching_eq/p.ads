package P is
   type Object is tagged null record;

   function "=" (O1, O2 : Object) return Boolean is (True) with
      Post'Class => "="'Result;

   type Child is new Object with record
      F : Integer;
   end record;

   function "=" (O1, O2 : Child) return Boolean is (True);
end P;
