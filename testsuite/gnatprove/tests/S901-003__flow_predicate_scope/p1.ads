package P1 is

    type T is Array (Positive range <>) of Integer with Predicate => True;

    package Q is
       function F (X : T) return Integer is (0);
    end Q;

end P1;
