
    procedure Main with SPARK_Mode => On is
        type Integer_access is access Integer;
        function New_integer return Integer_access
        is
            pragma SPARK_Mode(Off);
        begin
            return new Integer'(0);
        end New_integer;
        i : constant Integer_access := New_integer;
    begin
        null;
    end Main;
