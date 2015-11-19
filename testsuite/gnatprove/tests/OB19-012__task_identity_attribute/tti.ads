with Ada.Task_Identification;

package TTI is

    task T;

    function Identity return Ada.Task_Identification.Task_Id is (T'Identity) with Volatile_Function;

end;
