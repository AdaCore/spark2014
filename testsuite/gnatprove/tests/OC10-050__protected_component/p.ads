package P is

   protected type PT is
      procedure Dummy;
      pragma Attach_Handler (Dummy, 10);
   end;

   type Some_Record is
   record
      PO : PT;
   end record;
   pragma Volatile (Some_Record);

   PR : Some_Record with Volatile; -- record with protected component

end P;
