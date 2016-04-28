----------------------------------------------------------------
-- IRONSIDES - DNS SERVER
--
-- By: Martin C. Carlisle and Barry S. Fagin
--     Department of Computer Science
--     United States Air Force Academy
--
-- Modified by: Altran UK Limited
--
-- This is free software; you can redistribute it and/or
-- modify without restriction.  We do ask that you please keep
-- the original author information, and clearly indicate if the
-- software has been modified.
--
-- This software is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty
-- of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
----------------------------------------------------------------

package Task_Limit is
   Max_Tasks : constant Integer := 100;
   subtype Task_Count_Subtype is Integer range 0 .. Max_Tasks;

   protected type Task_Count_Type is
      pragma Priority(0);

      --  function Valid_Number_Of_Tasks return Boolean;

      procedure Increment (Success : out Boolean)
        with Global  => null,
             Depends => ((Success, Task_Count_Type) => Task_Count_Type); --  ,
             --  Pre     => Valid_Number_Of_Tasks,
             --  Post    => Valid_Number_Of_Tasks;

      procedure Decrement
        with Global  => null,
             Depends => (Task_Count_Type =>+ null); --  ,
             --  Pre     => Valid_Number_Of_Tasks,
             --  Post    => Valid_Number_Of_Tasks;
   private
      Task_Count : Task_Count_Subtype := 0;
   end Task_Count_Type;
end Task_Limit;
