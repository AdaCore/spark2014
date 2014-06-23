package P is
   subtype Index is Integer range 1 .. 10;
   type My_Array is array (Index) of Index;

   procedure P (F : in out My_Array);
end P;
