package Test with SPARK_Mode is

    X, Y : Integer;

    function Test_Post return Boolean is
      (X = 3 and then Y = 5) with Ghost;

    procedure Test_Main
    with Post => Test_Post;

end test;
