with Ada.Text_IO;
with System.Storage_Elements;

package Pack is

   pragma SPARK_Mode (Off);

   package Address_Value_IO is
     new Ada.Text_IO.Modular_IO (System.Storage_Elements.Integer_Address);

   function Address_To_Hex (Adder: System.Address) return String;

end Pack;
