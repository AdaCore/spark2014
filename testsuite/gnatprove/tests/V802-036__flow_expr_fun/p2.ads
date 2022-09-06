with P1;

package P2 with SPARK_Mode => On is
    function F return Integer with Pre => P1.Call_Get_X;
end P2;
