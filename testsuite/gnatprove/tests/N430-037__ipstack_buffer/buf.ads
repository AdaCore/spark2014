package Buf with
  SPARK_Mode,
  Abstract_State => State
is
   type Buffer is record
      Data : Integer;
   end record;

   procedure P;
   --  dummy procedure to force a body
end Buf;
