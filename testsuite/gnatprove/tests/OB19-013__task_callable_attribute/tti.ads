with Ada.Task_Identification;

package TTI is

    task T;

    function Callable return Boolean is (T'Callable) with Volatile_Function;

end;
