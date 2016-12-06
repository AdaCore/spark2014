package body Terminating_Annotations with SPARK_Mode is
    function F_Not_SPARK (X : Natural) return Natural is (0) with
SPARK_Mode => Off;

    procedure Not_SPARK with SPARK_Mode => Off is
    begin
       loop
          null;
       end loop;
    end Not_SPARK;

    function F_Call (X : Natural) return Natural is
    begin
       Not_SPARK;
       return 0;
    end F_Call;
end Terminating_Annotations;
