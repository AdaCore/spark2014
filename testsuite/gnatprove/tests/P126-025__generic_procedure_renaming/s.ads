package S is

   generic
      type Element is range <>;
   procedure Not_Zero (E : Element) with Pre => E /= 0;

end S;
