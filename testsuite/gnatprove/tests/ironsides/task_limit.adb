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

--with ada.text_io;
package body Task_Limit is

   ---------------------
   -- Task_Count_Type --
   ---------------------

   protected body Task_Count_Type is

      ---------------------------
      -- Valid_Number_Of_Tasks --
      ---------------------------

      function Valid_Number_Of_Tasks return Boolean is
        (Task_Count in Task_Count_Subtype);

      ---------------
      -- Increment --
      ---------------

      procedure Increment (Success : out Boolean)
        with Refined_Post =>
               Task_Count in Task_Count_Subtype and
               (if Task_Count'Old = Max_Tasks then
                  Task_Count = Task_Count'Old and not Success) and
               (if Task_Count'Old < Max_Tasks then
                  Task_Count = Task_Count'Old + 1 and Success)
      is
      begin
         if Task_Count < Max_Tasks then
            Task_Count := Task_Count + 1;
            --Ada.Text_IO.Put_Line("increment : " & Integer'Image (Task_Count));
            Success := True;
         else
            Success := False;
         end if;
      end Increment;

      ---------------
      -- Decrement --
      ---------------

      procedure Decrement
        with Refined_Post =>
               Valid_Number_Of_Tasks and
               (if Task_Count'Old > 0 then
                  Task_Count = Task_Count'Old - 1) and
               (if Task_Count'Old = 0 then Task_Count = Task_Count'Old)
      is
      begin
         if Task_Count > 0 then
            Task_Count := Task_Count - 1;
         end if;
      end Decrement;

   end Task_Count_Type;

end Task_Limit;
