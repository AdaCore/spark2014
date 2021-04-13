procedure No_Return_Function with SPARK_Mode is
   function Raise_Program_Error return Boolean is
     (raise Program_Error)
   with No_Return;
begin
   null;
end No_Return_Function;
