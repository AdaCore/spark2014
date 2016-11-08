with System;

package body Legal is

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

   function F_01 return Integer
     with Volatile_Function
   is
   begin
      return PO_V3.F;
   end;
   --  OK

   function F_03 return Integer
     with Volatile_Function
   is
      Tmp : Integer;
   begin
      PO_V3.P (Tmp);
      return Tmp;
   end;
   --  Bad

   function F_04 return Integer
   is
      Tmp : Integer;
   begin
      PO_V3.P (Tmp);
      return Tmp;
   end;
   --  Bad

   function F_05 return Integer
     with Volatile_Function
   is
      Tmp : Integer;
   begin
      PO_V4.P (Tmp);
      return Tmp;
   end;
   --  Bad

   function F_06 return Integer
   is
      Tmp : Integer;
   begin
      PO_V4.P (Tmp);
      return Tmp;
   end;
   --  Bad

   procedure P_01 (X : out Integer)
   is
   begin
      X := PO_V3.F;
   end;
   --  OK

   procedure P_02 (X : out Integer)
   is
   begin
      PO_V3.P (X);
   end;
   --  OK

   procedure P_03 (X : out Integer)
   is
   begin
      PO_V4.P (X);
   end;
   --  OK

end Legal;
