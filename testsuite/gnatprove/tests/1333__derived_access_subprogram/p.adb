package body P is
   package body Ptr is
      function To_Handler (P : Ptr.H_Ptr) return Handler_Type
      is (Handler_Type (P));
   end Ptr;
end P;
