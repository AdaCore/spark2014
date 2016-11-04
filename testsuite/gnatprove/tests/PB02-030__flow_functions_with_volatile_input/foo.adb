with System;

package body Foo is

   V1 : Integer with
     Volatile, Async_Readers, Async_Writers, Effective_Writes,
     Address => System'To_Address (16#DEADBEEF#), Import;
   --  Lacks effective_reads

   V2 : Integer with
     Volatile,
     Address => System'To_Address (16#C0FFEE#), Import;
   --  Fully volatile

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

   protected PO_V3 is
      function F return Integer;
      procedure P (X : out Integer);
   end;

   protected PO_V4 is
      function F return Integer;
      procedure P (X : out Integer);
   end;

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

   function Test_01 return Integer
   is
      Tmp : Integer := V1;
   begin
      return Tmp;
   end;
   --  Bad

   function Test_02 return Integer
   is
      Tmp : Integer := V2;
   begin
      return Tmp;
   end;
   --  Bad

   function Test_03 return Integer
   with Volatile_Function
   is
      Tmp : Integer := V1;
   begin
      return Tmp;
   end;
   --  OK

   function Test_04 return Integer
   with Volatile_Function
   is
      Tmp : Integer := V2;
   begin
      return Tmp;
   end;
   --  Bad

   --  TODO: tests for functions and procedures using the POs

end Foo;
