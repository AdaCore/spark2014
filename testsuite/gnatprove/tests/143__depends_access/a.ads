package A with SPARK_Mode is
    type T is not null access Integer;
    procedure P (Param : in T)
      with
        Global => null,
        Depends =>
          (Param => Param);
end A;
