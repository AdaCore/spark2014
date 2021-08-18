generic
   type Custom_Index is range <>;
   type Custom_Byte is (<>);
   type Custom_Bytes is array (Custom_Index range <>) of Custom_Byte;
   type Custom_Bytes_Ptr is access all Custom_Bytes;
package Generic_Types with
  SPARK_Mode
is

   subtype Bytes_Ptr is Custom_Bytes_Ptr;

end Generic_Types;
