package P is
    type T is (A, B);

    package P1 is
       type T1 is limited private;
    private
       type T1 is new T;
    end P1;

    package P2 is
       use P1;
       type T2 is limited private;
    private
       type T2 is new T1;
    end P2;

end P;
