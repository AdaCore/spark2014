procedure Main is

   package Handler is
      subtype Handling_Range is Integer range 1 .. 5000;

      type Handler_Type is private;

      package Ptr is
         type H_Ptr is
           access procedure (Handle : Handling_Range; Handled : out Boolean);

         function To_Handler (P : H_Ptr) return Handler_Type;
      end Ptr;

   private

      type Handler_Type is new Ptr.H_Ptr;

      procedure Null_CB (Handle : Handling_Range; Handled : out Boolean);

      function Null_Handler return Handler_Type
      is (To_Handler (Null_CB'Access));

   end Handler;

   package body Handler is
      procedure Null_CB (Handle : Handling_Range; Handled : out Boolean) is
      begin
         null;
      end Null_CB;

      package body Ptr is
         function To_Handler (P : Ptr.H_Ptr) return Handler_Type
         is (Handler_Type (P));
      end Ptr;
   end Handler;

begin
   null;
end Main;
