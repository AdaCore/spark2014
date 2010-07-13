package Data_Model is

   pragma Pure (Data_Model);

   type Int32_T is range - 2 ** 31 .. 2 ** 31 - 1;
   for Int32_T'Value_Size use 32;

end Data_Model;
