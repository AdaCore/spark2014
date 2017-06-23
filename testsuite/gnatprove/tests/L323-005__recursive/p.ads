package P is
    function Id (N : Natural) return Natural with
      Post => Id'Result = (if N = 0 then 0 else Id(N-1)+1);

    function Bad return Boolean is (if True then not Bad);

    procedure Use_Bad with Post => False;

    function Down (X : Positive) return Positive is
       (if X = 1 then X else Down (X - 1) + 1);
    pragma Annotate (GNATprove, Terminating, Down);

    procedure Use_Down (X : Positive) with
      Pre  => X > 1,
      Post => Down (X) = Down (X - 1) + 1;
end P;
