package P is

   type T is new Integer with Predicate => Blocking;

   function Blocking return Boolean with Post => Blocking'Result;

   protected PT is
      procedure Dummy;
   end;

end;
