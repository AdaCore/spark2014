with Ada.Task_Identification;

package TTI is

    task T;

    function Terminated return Boolean is (T'Terminated) with Volatile_Function;

end;
