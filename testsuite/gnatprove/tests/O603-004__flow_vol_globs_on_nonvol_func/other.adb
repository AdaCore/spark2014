package body Other is
   Hidden : Integer := 0
     with Volatile,
          Async_Writers;

   procedure Vol_Proc (X : out Integer) is
   begin
      X := Hidden;
   end Vol_Proc;
end Other;
