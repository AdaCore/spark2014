package Q is

   protected PO3 is
      procedure Proc with Attach_Handler => 1; --@INTERRUPT_RESERVED:FAIL
   end;

end;
