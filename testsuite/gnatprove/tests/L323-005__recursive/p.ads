package P is
    function Id (N : Natural) return Natural with
      Post => Id'Result = (if N = 0 then 0 else Id(N-1)+1);
end P;
