package P is

   X : Boolean := True;

   protected PO1 is
      procedure Proc1 with Global => (In_Out => X);
      pragma Attach_Handler (Proc1, 10); --@INTERRUPT_RESERVED:FAIL
   end;

   protected PO2 is
      procedure Proc2 with Global => (In_Out => X);
      pragma Attach_Handler (Proc2, 11); --@INTERRUPT_RESERVED:FAIL
   end;
end;
