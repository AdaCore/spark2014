package P is
   type T is null record;

   C : T;

   function Name (X : T) return String;
end;
