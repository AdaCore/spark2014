package P is

   subtype T is Integer with Dynamic_Predicate => F;

   function F return Boolean;

end;
