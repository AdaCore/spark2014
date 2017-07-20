with System;

package body Illegal is

   protected PO_V3 is
      function F return Integer;
      procedure P (X : out Integer);
   end;

   protected PO_V4 is
      function F return Integer;
      procedure P (X : out Integer);
   end;

   V3 : Integer with
     Volatile, Async_Readers, Async_Writers, Effective_Writes,
     Address => System'To_Address (16#DEADBEEF#), Import,
     Part_Of => PO_V3;
   --  Lacks effective_reads

   V4 : Integer with
     Volatile,
     Address => System'To_Address (16#C0FFEE#), Import,
     Part_Of => PO_V4;
   --  Fully volatile

   protected body PO_V3 is
      function F return Integer -- OK
      is
         Tmp : Integer := V3;
      begin
         return Tmp;
      end;

      procedure P (X : out Integer) -- OK
      is
      begin
         X := V3;
      end;
   end;

   protected body PO_V4 is
      function F return Integer -- Not OK since we have a side-effect here
      is
         Tmp : Integer := V4;
      begin
         return Tmp;
      end;

      procedure P (X : out Integer) -- OK
      is
      begin
         X := V4;
      end;
   end;

   function F2 return Integer is (PO_V3.F);
   -- Not OK because it calls volatile function in interfering context

end Illegal;
