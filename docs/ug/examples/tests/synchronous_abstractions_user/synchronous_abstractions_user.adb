with Synchronous_Abstractions;
package body Synchronous_Abstractions_User with SPARK_Mode is
   task body Use_Synchronized_State is
   begin
      loop
         Synchronous_Abstractions.Do_Something;
      end loop;
   end Use_Synchronized_State;
end Synchronous_Abstractions_User;
