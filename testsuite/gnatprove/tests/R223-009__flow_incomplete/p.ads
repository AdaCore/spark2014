package P is
   X : Boolean := True;

   function F1 return Boolean is (X) with Global  => null;
   function F2 return Boolean is (X) with Depends => (F2'Result => null);
   function F3 return Boolean is (X) with Pure_Function;

end;
