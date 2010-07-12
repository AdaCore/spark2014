------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package body Constants is
   procedure CND is
   begin
      System.Machine_Code.Asm
        (ASCII.LF & "->CND:%0:" & Name & ":%1:" & Name,
         Inputs  => (Integer'Asm_Input ("i", 0),
                     Integer'Asm_Input ("i", Val)),
         Volatile => True);
   end CND;

   procedure C00 is new CND
     ("Address_Size", Standard'Address_Size);
   procedure C01 is new CND
     ("Default_Bit_Order", System.Bit_Order'Pos (System.Default_Bit_Order));
   procedure C02 is new CND
     ("Network_Bit_Order", System.Bit_Order'Pos (System.High_Order_First));

end Constants;
