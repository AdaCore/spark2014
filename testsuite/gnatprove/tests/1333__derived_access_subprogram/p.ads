package P is

   type Handler_Type is private;

   package Ptr is
      type H_Ptr is access procedure;
      function To_Handler (P : H_Ptr) return Handler_Type;
   end Ptr;

private
   type Handler_Type is new Ptr.H_Ptr;
end P;
