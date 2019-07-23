pragma SPARK_Mode;
package Lists is

   type T;

   type T_Ptr is access T;

   type T is record
      Data : Integer;
      Next : T_Ptr;
   end record;

   procedure Prepend (List : in out T_Ptr);
   procedure Remove_Head (List : in out T_Ptr);

end Lists;
