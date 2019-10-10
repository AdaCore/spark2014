package P2 is

    type T1 is Array (Positive range <>) of Integer with Predicate => True;

    package Q is

        subtype T2 is T1
            with Predicate => True;

    end Q;

    package R is

        function G return Integer is (0);
        procedure Dummy (Raw_Data: in Q.T2);

    end R;

end P2;
