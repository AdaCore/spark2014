-- pragma SPARK_Mode; -- Note that SPARK_Mode is not allowed in generic
                      -- declarations, but instantations may have SPARK_Mode.
with System.Storage_Elements;
package body Parent.Child
is

   Port : Integer
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (In_Address);

   function Read_Switch return Parent.Switch_Pos
   is
      Raw_Value : Integer;
   begin
      Raw_Value := Port;  -- try changing to Raw_Value := Port + 1;
      case Raw_Value is
         when 0 => return On;
         when 1 => return Off;
         when others => return Unknown;
      end case;
   end Read_Switch;

end Parent.Child;
