with Data_Buffer.Context;

package Instance
with SPARK_Mode => On
is

   package Context is new Data_Buffer.Context
     (Header_Type     => Integer,
      Null_Header     => 0,
      Header_Capacity => 4,
      Item_Type       => Integer,
      Null_Item       => 0,
      Item_Capacity   => 16);

end Instance;
