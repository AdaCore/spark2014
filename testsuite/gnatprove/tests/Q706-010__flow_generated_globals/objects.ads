package Objects is
   type T is interface;
   procedure Proc (V : T) is abstract;

   type U is new T with null record;
   overriding procedure Proc (V : U);
end Objects;
