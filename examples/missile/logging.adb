-- Implementation of logging
--
-- $Log: logging.adb,v $
-- Revision 1.1  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
--
with Airspeed.Log,Clock;
package body Logging is
   type Lru_Checks is array(Logging_Cfg.LRU_name) of Boolean;

   -- Testing state
   Are_Logging : Boolean := False;
   Log_Handle  : Ada.Text_Io.File_Type;
   LRU_Active  : Lru_Checks := Lru_Checks'(others => False);

   procedure Finish_Logging
   is
   begin
      if Are_Logging then
	 Ada.Text_Io.Put_Line("Logging finished");
         Ada.Text_Io.Close(Log_Handle);
         Are_Logging := False;
      else
         -- Already stopped
         null;
      end if;
   end Finish_Logging;

   procedure Start_Logging(Filename : in String)
   is
      Data_Line : Logging_Cfg.Log_String;
   begin
      -- Finish off any logging we're doing
      Finish_Logging;
      --- Now open the new file for writing
      Ada.Text_Io.Create(File => Log_Handle,
			 Mode => Ada.Text_Io.Out_File,
			 Name => Filename,
			 Form => "");
      if not Ada.Text_Io.Is_Open(Log_Handle) then
         -- Failed to open log
         Are_Logging := False;
	 Ada.Text_Io.Put_Line("FAILED to open log file '" & 
				Filename & "'");
      else
	 Ada.Text_Io.Put_Line("Logging started in '" & Filename & "'");
         -- Succeeded in opening log
         Are_Logging := True;
         -- Dump the header information
	 Ada.Text_Io.Put_Line
	   (File => Log_Handle,
	    Item => "BEGIN HEADER");
         -- TODO: extent to all relevant LRUs
         Data_Line := Airspeed.Log.Header;
         Ada.Text_Io.Put_Line
	   (File => Log_Handle,
	    Item => Logging_Cfg.Log_String_Ops.To_String(Data_Line));
	 Ada.Text_Io.Put_Line
	   (File => Log_Handle,
	    Item => "END HEADER");
      end if;
   end Start_Logging;

   procedure Log
   is
      Data_Line : Logging_Cfg.Log_String;
      Time_Now : Clock.Millisecond;
      Time_Valid : Boolean;
   begin
      if Are_Logging then
         if Lru_Active(Test_Keywords.Airspeed) then
            Airspeed.Log.Data(Data_Line);
            Ada.Text_Io.Put_Line
	      (File => Log_Handle,
	       Item => Logging_Cfg.Log_String_Ops.To_String(Data_Line));
         end if;
         --TODO: add other units here as logging implemented
	 
	 -- Now mark with time we read this
	 Clock.Read(T     => Time_Now,
		    Valid => Time_Valid);
	 Ada.Text_Io.Put_Line
	   (File => Log_handle,
	    Item => "LOG: " & Clock.Millisecond'image(Time_Now));
      end if;
   end Log;
   
   -- This procedure does work including dumping logging
   -- data to file.
   procedure Process_Logging
   is
      Cmd      : Logging_Cfg.Log_Command;
      Filename : String(1..256) := (others => ASCII.Nul);
      Last     : Natural;
      Enabling : Boolean;
      Lru      : Logging_Cfg.Lru_Name;
   begin
      Logging_Cfg.Log_Io.Get(Cmd);
      case Cmd is
         when Logging_Cfg.Start =>
            Finish_Logging;
            -- In any case, open up a new file
            Ada.Text_Io.Get_Line
              (File => Ada.Text_Io.Standard_Input,
               Item => Filename,
               Last => Last);
            -- Start_Logging(Filename(1..Last));
	    Start_Logging("airspeed.log");
	    
         when Logging_Cfg.Stop =>
            Finish_Logging;

         when Logging_Cfg.Enable | Logging_Cfg.Disable =>
            Enabling := (Cmd = Logging_Cfg.Enable);
            -- Read the unit name to enable or disable
            Logging_Cfg.Lru_Io.Get(LRU);
            Lru_Active(LRU) := Enabling;
	    Ada.Text_Io.Put
	      ("Logging in " & Logging_Cfg.Lru_name'image(LRU));
	    if Enabling then
	       Ada.Text_Io.Put_Line(" enabled");
	    else
	       Ada.text_io.Put_line(" disabled");
	    end if;
      end case;
   end Process_Logging;


end Logging;
