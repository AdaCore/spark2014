with System.Storage_Elements,
     Externals.Temperature,
     Externals.Pressure,
     Externals.Main_Display,
     Externals.Secondary_Display;

package body Externals
  with SPARK_Mode,
       Refined_State => (Combined_Inputs => (Externals.Temperature.State,
                                             Externals.Pressure.State),
                         -- Both Temperature and
                         -- Pressure are inputs only.

                         Displays => (Externals.Main_Display.State,
                                      Externals.Secondary_Display.State),
                         -- Both Main_Display and
                         -- Secondary_Display are outputs only.

                         Complex_Device => (Saved_Value,
                                            Out_Reg,
                                            In_Reg))
                         -- Complex_Device is a mixture of inputs, outputs and
                         -- non-volatile constituents.
is
   procedure Read (Combined_Value : out Integer)
     with Refined_Global  => (Temperature.State, Pressure.State),
          Refined_Depends => (Combined_Value => (Temperature.State,
                                                 Pressure.State))
   is
      Temp,
      Press : Integer;
      K : constant := 1234;
   begin
      Temperature.Read (Temp);
      Pressure.Read (Press);
      Combined_Value := Press + Temp * K;-- Some_Function_Of (Temp, Pressure);
   end Read;

   procedure Display (D_Main, D_Secondary : in String)
     with Refined_Global  => (Output => (Main_Display.State,
                                         Secondary_Display.State)),
          Refined_Depends => ((Main_Display.State,
                               Secondary_Display.State) => (D_Main,
                                                            D_Secondary))
   is
   begin
      Main_Display.Display (D_Main);
      Secondary_Display.Display (D_Secondary);
   end Display;

   -------------------- Complex Device --------------------

   Saved_Value : Integer := 0;  -- Initialized as required.

   Out_Reg : Integer
     with Volatile,
          Async_Readers,
          Effective_Writes, -- Every value written to the port is significant.
          Address  => System.Storage_Elements.To_Address (16#ACECAFE0#);

   In_Reg : Integer
     with Volatile,
          Async_Writers,
          Address  => System.Storage_Elements.To_Address (16#A11CAFE0#);

   function Last_Value_Sent return Integer
     with Refined_Global => Saved_Value -- Refined_Global aspect only
                                        -- refers to a non-volatile
                                        -- constituent.
   is
   begin
      return Saved_Value;
   end Last_Value_Sent;

   procedure Output_Value (Value : in Integer)
     with Refined_Global  => (Input  => In_Reg,
                              Output => Out_Reg,
                              In_Out => Saved_Value),
     --  Refined_Global aspect refers to both volatile
     --  and non-volatile constituents.

          Refined_Depends => ((Out_Reg,
                               Saved_Value) => (Saved_Value,
                                                Value),
                              null => In_Reg)
   is
      Ready  : constant Integer := 42;
      Status : Integer;
   begin
      if Saved_Value /= Value then
         loop
            Status := In_Reg;  -- In_Reg has the property Async_Writers
                               -- and may appear on RHS of assignment
                               -- but not in a condition.
            exit when Status = Ready;
         end loop;

         Out_Reg := Value;  -- Out_Reg has the property Async_Readers
                            -- and the assigned value will be consumed.
         Saved_Value := Value;  -- Writing to the Out_Reg also results
                                -- in updating Saved_Value.
      end if;
   end Output_Value;
end Externals;
