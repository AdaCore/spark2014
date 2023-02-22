procedure Main is

   type T is range 0 .. 100;

   function Is_Null (X : T) return Boolean;

   subtype S is T with Predicate => not Is_Null (S);

   function Helper (X : S) return Boolean;

   function Is_Null (X : T) return Boolean is
   begin
      if X > 10 then
        return Helper (X);
      else
         return X = 0;
      end if;
   end Is_Null;

   function Helper (X : S) return Boolean is
   begin
      return True;
   end Helper;
begin
   null;
end Main;
