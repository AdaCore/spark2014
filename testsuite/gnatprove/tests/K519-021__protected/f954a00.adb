

     --==================================================================--


package body F954A00 is   -- Printer server abstraction.
   pragma SPARK_Mode (Off);

   protected body Printers is

      procedure Start_Printing (File_Name : String) is
      begin
         Ready := False;                              -- Block other requests
         Done  := False;                              -- for this printer
         -- Send data to the printer...               -- and begin printing.
      end Start_Printing;


      -- Set the "not ready" one-shot
      entry Done_Printing when Ready is               -- Callers wait here
      begin                                           -- until printing is
         Done := True;                                -- done (signaled by a
      end Done_Printing;                              -- printer interrupt).


      procedure Handle_Interrupt is                   -- Called when the
      begin                                           -- printer interrupts,
         Ready := True;                               -- indicating that
      end Handle_Interrupt;                           -- printing is done.


      function Available return Boolean is            -- Artifice for test
      begin                                           -- purposes: checks
         return (Ready);                              -- whether printer is
      end Available;                                  -- still printing.


      function Is_Done return Boolean is              -- Artifice for test
      begin                                           -- purposes: checks
         return (Done);                               -- whether Done_Printing
      end Is_Done;                                    -- entry was executed.

   end Printers;


end F954A00;
